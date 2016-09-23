{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE CPP #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE FlexibleContexts, FlexibleInstances, MultiParamTypeClasses #-}
{-# LANGUAGE UndecidableInstances #-}
{-# OPTIONS_GHC -fno-warn-orphans -fno-warn-missing-fields #-}
-- overlapping instances is for automatic lifting
-- while avoiding an orphan of Lift for Text
{-# LANGUAGE OverlappingInstances #-}
-- | This module provides utilities for creating backends. Regular users do not
-- need to use this module.
module Database.Persist.TH
  ( module Database.Persist.TH
  , MkPersistSettings(..)
  , EntityJSON(..)
  , lensPTH
  , packPTH
  )
  where

import Prelude hiding ((++), take, concat, splitAt, exp)
import Database.Persist
import Database.Persist.Sql (Migration, migrate, SqlBackend)
import Database.Persist.TH.Internal
import Database.Persist.Quasi
import Language.Haskell.TH.Quote
import Language.Haskell.TH.Syntax
import Control.Monad ((<=<))
import qualified System.IO as SIO
import Data.Text (pack, unpack)
import Data.Text.Encoding (decodeUtf8)
import qualified Data.Text.IO as TIO
import qualified Data.Map as M
import qualified Data.HashMap.Strict as HM
import Data.Aeson.Compat (eitherDecodeStrict')
import qualified Data.Text.Encoding as TE

-- | Converts a quasi-quoted syntax into a list of entity definitions, to be
-- used as input to the template haskell generation code (mkPersist).
persistWith :: PersistSettings -> QuasiQuoter
persistWith ps = QuasiQuoter
    { quoteExp = parseReferences ps . pack
    }

-- | Apply 'persistWith' to 'upperCaseSettings'.
persistUpperCase :: QuasiQuoter
persistUpperCase = persistWith upperCaseSettings

-- | Apply 'persistWith' to 'lowerCaseSettings'.
persistLowerCase :: QuasiQuoter
persistLowerCase = persistWith lowerCaseSettings

-- | Same as 'persistWith', but uses an external file instead of a
-- quasiquotation.
persistFileWith :: PersistSettings -> FilePath -> Q Exp
persistFileWith ps fp = do
#ifdef GHC_7_4
    qAddDependentFile fp
#endif
    h <- qRunIO $ SIO.openFile fp SIO.ReadMode
    qRunIO $ SIO.hSetEncoding h SIO.utf8_bom
    s <- qRunIO $ TIO.hGetContents h
    parseReferences ps s

-- calls parse to Quasi.parse individual entities in isolation
-- afterwards, sets references to other entities
parseReferences :: PersistSettings -> Text -> Q Exp
parseReferences ps s = lift $
     map (mkEntityDefSqlTypeExp embedEntityMap entMap) noCycleEnts
  where
    entMap = M.fromList $ map (\ent -> (entityHaskell ent, ent)) noCycleEnts
    noCycleEnts = map breakCycleEnt entsWithEmbeds
    -- every EntityDef could reference each-other (as an EmbedRef)
    -- let Haskell tie the knot
    embedEntityMap = M.fromList $ map (\ent -> (entityHaskell ent, toEmbedEntityDef ent)) entsWithEmbeds
    entsWithEmbeds = map setEmbedEntity rawEnts
    setEmbedEntity ent = ent
      { entityFields = map (setEmbedField (entityHaskell ent) embedEntityMap) $ entityFields ent
      }
    rawEnts = parse ps s

    -- self references are already broken
    -- look at every emFieldEmbed to see if it refers to an already seen HaskellName
    -- so start with entityHaskell ent and accumulate embeddedHaskell em
    breakCycleEnt entDef =
      let entName = entityHaskell entDef
      in  entDef { entityFields = map (breakCycleField entName) $ entityFields entDef }

    breakCycleField entName f@(FieldDef { fieldReference = EmbedRef em }) =
      f { fieldReference = EmbedRef $ breakCycleEmbed [entName] em }
    breakCycleField _ f = f

    breakCycleEmbed ancestors em =
        em { embeddedFields = map (breakCycleEmField $ emName : ancestors)
                                  (embeddedFields em)
           }
      where
        emName = embeddedHaskell em

    breakCycleEmField ancestors emf = case embeddedHaskell <$> membed of
        Nothing -> emf
        Just embName -> if embName `elem` ancestors
          then emf { emFieldEmbed = Nothing, emFieldCycle = Just embName }
          else emf { emFieldEmbed = breakCycleEmbed ancestors <$> membed }
      where
        membed = emFieldEmbed emf



stripId :: FieldType -> Maybe Text
stripId (FTTypeCon Nothing t) = stripSuffix "Id" t
stripId _ = Nothing

foreignReference :: FieldDef -> Maybe HaskellName
foreignReference field = case fieldReference field of
    ForeignRef ref _ -> Just ref
    _              -> Nothing


-- fieldSqlType at parse time can be an Exp
-- This helps delay setting fieldSqlType until lift time
data EntityDefSqlTypeExp = EntityDefSqlTypeExp EntityDef SqlTypeExp [SqlTypeExp]
                           deriving Show

data SqlTypeExp = SqlTypeExp FieldType
                | SqlType' SqlType
                deriving Show

instance Lift SqlTypeExp where
    lift (SqlType' t)       = lift t
    lift (SqlTypeExp ftype) = return st
      where
        typ = ftToType ftype
        mtyp = (ConT ''Proxy `AppT` typ)
        typedNothing = SigE (ConE 'Proxy) mtyp
        st = VarE 'sqlType `AppE` typedNothing

data FieldsSqlTypeExp = FieldsSqlTypeExp [FieldDef] [SqlTypeExp]

instance Lift FieldsSqlTypeExp where
    lift (FieldsSqlTypeExp fields sqlTypeExps) =
        lift $ zipWith FieldSqlTypeExp fields sqlTypeExps

data FieldSqlTypeExp = FieldSqlTypeExp FieldDef SqlTypeExp
instance Lift FieldSqlTypeExp where
    lift (FieldSqlTypeExp (FieldDef{..}) sqlTypeExp) =
      [|FieldDef fieldHaskell fieldDB fieldType $(lift sqlTypeExp) fieldAttrs fieldStrict fieldReference|]

instance Lift EntityDefSqlTypeExp where
    lift (EntityDefSqlTypeExp ent sqlTypeExp sqlTypeExps) =
        [|ent { entityFields = $(lift $ FieldsSqlTypeExp (entityFields ent) sqlTypeExps)
              , entityId = $(lift $ FieldSqlTypeExp (entityId ent) sqlTypeExp)
              }
        |]

instance Lift ReferenceDef where
    lift NoReference = [|NoReference|]
    lift (ForeignRef name ft) = [|ForeignRef name ft|]
    lift (EmbedRef em) = [|EmbedRef em|]
    lift (CompositeRef cdef) = [|CompositeRef cdef|]
    lift (SelfReference) = [|SelfReference|]

instance Lift EmbedEntityDef where
    lift (EmbedEntityDef name fields) = [|EmbedEntityDef name fields|]

instance Lift EmbedFieldDef where
    lift (EmbedFieldDef name em cyc) = [|EmbedFieldDef name em cyc|]

type EmbedEntityMap = M.Map HaskellName EmbedEntityDef
type EntityMap = M.Map HaskellName EntityDef

data FTTypeConDescr = FTKeyCon deriving Show
mEmbedded :: EmbedEntityMap -> FieldType -> Either (Maybe FTTypeConDescr) EmbedEntityDef
mEmbedded _ (FTTypeCon Just{} _) = Left Nothing
mEmbedded ents (FTTypeCon Nothing n) = let name = HaskellName n in
    maybe (Left Nothing) Right $ M.lookup name ents
mEmbedded ents (FTList x) = mEmbedded ents x
mEmbedded ents (FTApp x y) =
  -- Key converts an Record to a RecordId
  -- special casing this is obviously a hack
  -- This problem may not be solvable with the current QuasiQuoted approach though
  if x == FTTypeCon Nothing "Key"
    then Left $ Just FTKeyCon
    else mEmbedded ents y

setEmbedField :: HaskellName -> EmbedEntityMap -> FieldDef -> FieldDef
setEmbedField entName allEntities field = field
  { fieldReference = case fieldReference field of
      NoReference ->
        case mEmbedded allEntities (fieldType field) of
            Left _ -> case stripId $ fieldType field of
                Nothing -> NoReference
                Just name -> case M.lookup (HaskellName name) allEntities of
                    Nothing -> NoReference
                    Just x -> ForeignRef (HaskellName name)
                                    -- This can get corrected in mkEntityDefSqlTypeExp
                                    (FTTypeCon (Just "Data.Int") "Int64")
            Right em -> if embeddedHaskell em /= entName
              then EmbedRef em
              else if maybeNullable field
                     then SelfReference
                     else case fieldType field of
                       FTList _ -> SelfReference
                       _ -> error $ unpack $ unHaskellName entName
                           `mappend` ": a self reference must be a Maybe"
      existing@_   -> existing
  }

mkEntityDefSqlTypeExp :: EmbedEntityMap -> EntityMap -> EntityDef -> EntityDefSqlTypeExp
mkEntityDefSqlTypeExp emEntities entMap ent = EntityDefSqlTypeExp ent
    (getSqlType $ entityId ent)
    $ (map getSqlType $ entityFields ent)
  where
    getSqlType field = maybe
        (defaultSqlTypeExp field)
        (SqlType' . SqlOther)
        (listToMaybe $ mapMaybe (stripPrefix "sqltype=") $ fieldAttrs field)


    -- In the case of embedding, there won't be any datatype created yet.
    -- We just use SqlString, as the data will be serialized to JSON.
    defaultSqlTypeExp field = case mEmbedded emEntities ftype of
        Right _ -> SqlType' SqlString
        Left (Just FTKeyCon) -> SqlType' SqlString
        Left Nothing -> case fieldReference field of
            ForeignRef refName ft  -> case M.lookup refName entMap of
                Nothing  -> SqlTypeExp ft
                -- A ForeignRef is blindly set to an Int64 in setEmbedField
                -- correct that now
                Just ent -> case entityPrimary ent of
                    Nothing -> SqlTypeExp ft
                    Just pdef -> case compositeFields pdef of
                        [] -> error "mkEntityDefSqlTypeExp: no composite fields"
                        [x] -> SqlTypeExp $ fieldType x
                        _ -> SqlType' $ SqlOther "Composite Reference"
            CompositeRef _  -> SqlType' $ SqlOther "Composite Reference"
            _ -> case ftype of
                    -- In the case of lists, we always serialize to a string
                    -- value (via JSON).
                    --
                    -- Normally, this would be determined automatically by
                    -- SqlTypeExp. However, there's one corner case: if there's
                    -- a list of entity IDs, the datatype for the ID has not
                    -- yet been created, so the compiler will fail. This extra
                    -- clause works around this limitation.
                    FTList _ -> SqlType' SqlString
                    _ -> SqlTypeExp ftype
      where
        ftype = fieldType field

-- | Create data types and appropriate 'PersistEntity' instances for the given
-- 'EntityDef's. Works well with the persist quasi-quoter.
mkPersist :: MkPersistSettings -> [EntityDef] -> Q [Dec]
mkPersist mps ents' = do
    x <- fmap mconcat $ mapM (persistFieldFromEntity mps) ents
    y <- fmap mconcat $ mapM (mkEntity entMap mps) ents
    z <- fmap mconcat $ mapM (mkJSON mps) ents
    return $ mconcat [x, y, z]
  where
    ents = map fixEntityDef ents'
    entMap = M.fromList $ map (\ent -> (entityHaskell ent, ent)) ents

-- | Create an @MkPersistSettings@ with default values.
mkPersistSettings :: Type -- ^ Value for 'mpsBackend'
                  -> MkPersistSettings
mkPersistSettings t = MkPersistSettings
    { mpsBackend = t
    , mpsGeneric = False
    , mpsPrefixFields = True
    , mpsEntityJSON = Just EntityJSON
        { entityToJSON = 'entityIdToJSON
        , entityFromJSON = 'entityIdFromJSON
        }
    , mpsGenerateLenses = False
    }

-- | Use the 'SqlPersist' backend.
sqlSettings :: MkPersistSettings
sqlSettings = mkPersistSettings $ ConT ''SqlBackend

-- | Same as 'sqlSettings'.
--
-- Since 1.1.1
sqlOnlySettings :: MkPersistSettings
sqlOnlySettings = sqlSettings
{-# DEPRECATED sqlOnlySettings "use sqlSettings" #-}

-- | Creates a single function to perform all migrations for the entities
-- defined here. One thing to be aware of is dependencies: if you have entities
-- with foreign references, make sure to place those definitions after the
-- entities they reference.
mkMigrate :: String -> [EntityDef] -> Q [Dec]
mkMigrate fun allDefs = do
    body' <- body
    return
        [ SigD (mkName fun) typ
        , FunD (mkName fun) [normalClause [] body']
        ]
  where
    defs = filter isMigrated allDefs
    isMigrated def = not $ "no-migrate" `elem` entityAttrs def
    typ = ConT ''Migration
    entMap = M.fromList $ map (\ent -> (entityHaskell ent, ent)) allDefs
    body :: Q Exp
    body =
        case defs of
            [] -> [|return ()|]
            _  -> do
              defsName <- newName "defs"
              defsStmt <- do
                defs' <- mapM (liftAndFixKeys entMap) defs
                let defsExp = ListE defs'
                return $ LetS [ValD (VarP defsName) (NormalB defsExp) []]
              stmts <- mapM (toStmt $ VarE defsName) defs
              return (DoE $ defsStmt : stmts)
    toStmt :: Exp -> EntityDef -> Q Stmt
    toStmt defsExp ed = do
        u <- liftAndFixKeys entMap ed
        m <- [|migrate|]
        return $ NoBindS $ m `AppE` defsExp `AppE` u

-- | Save the @EntityDef@s passed in under the given name.
mkSave :: String -> [EntityDef] -> Q [Dec]
mkSave name' defs' = do
    let name = mkName name'
    defs <- lift defs'
    return [ SigD name $ ListT `AppT` ConT ''EntityDef
           , FunD name [normalClause [] defs]
           ]

-- | Apply the given list of functions to the same @EntityDef@s.
--
-- This function is useful for cases such as:
--
-- >>> share [mkSave "myDefs", mkPersist sqlSettings] [persistLowerCase|...|]
share :: [[EntityDef] -> Q [Dec]] -> [EntityDef] -> Q [Dec]
share fs x = fmap mconcat $ mapM ($ x) fs

-- | Generate a 'DeleteCascade' instance for the given @EntityDef@s.
mkDeleteCascade :: MkPersistSettings -> [EntityDef] -> Q [Dec]
mkDeleteCascade mps defs = do
    let deps = concatMap getDeps defs
    mapM (go deps) defs
  where
    getDeps :: EntityDef -> [Dep]
    getDeps def =
        concatMap getDeps' $ entityFields $ fixEntityDef def
      where
        getDeps' :: FieldDef -> [Dep]
        getDeps' field@FieldDef {..} =
            case foreignReference field of
                Just name ->
                     return Dep
                        { depTarget = name
                        , depSourceTable = entityHaskell def
                        , depSourceField = fieldHaskell
                        , depSourceNull  = nullable fieldAttrs
                        }
                Nothing -> []
    go :: [Dep] -> EntityDef -> Q Dec
    go allDeps EntityDef{entityHaskell = name} = do
        let deps = filter (\x -> depTarget x == name) allDeps
        key <- newName "key"
        let del = VarE 'delete
        let dcw = VarE 'deleteCascadeWhere
        just <- [|Just|]
        filt <- [|Filter|]
        eq <- [|Eq|]
        left <- [|Left|]
        let mkStmt :: Dep -> Stmt
            mkStmt dep = NoBindS
                $ dcw `AppE`
                  ListE
                    [ filt `AppE` ConE filtName
                           `AppE` (left `AppE` val (depSourceNull dep))
                           `AppE` eq
                    ]
              where
                filtName = filterConName' mps (depSourceTable dep) (depSourceField dep)
                val (Nullable ByMaybeAttr) = just `AppE` VarE key
                val _                      =             VarE key



        let stmts :: [Stmt]
            stmts = map mkStmt deps `mappend`
                    [NoBindS $ del `AppE` VarE key]

        let entityT = genericDataType mps name backendT

        return $
            instanceD
            [ mkClassP ''PersistQuery [backendT]
            , mkEqualP (ConT ''PersistEntityBackend `AppT` entityT) (ConT ''BaseBackend `AppT` backendT)
            ]
            (ConT ''DeleteCascade `AppT` entityT `AppT` backendT)
            [ FunD 'deleteCascade
                [normalClause [VarP key] (DoE stmts)]
            ]


-- | Automatically creates a valid 'PersistField' instance for any datatype
-- that has valid 'Show' and 'Read' instances. Can be very convenient for
-- 'Enum' types.
derivePersistField :: String -> Q [Dec]
derivePersistField s = do
    ss <- [|SqlString|]
    tpv <- [|PersistText . pack . show|]
    fpv <- [|\dt v ->
                case fromPersistValue v of
                    Left e -> Left e
                    Right s' ->
                        case reads $ unpack s' of
                            (x, _):_ -> Right x
                            [] -> Left $ pack "Invalid " ++ pack dt ++ pack ": " ++ s'|]
    return
        [ persistFieldInstanceD False (ConT $ mkName s)
            [ FunD 'toPersistValue
                [ normalClause [] tpv
                ]
            , FunD 'fromPersistValue
                [ normalClause [] (fpv `AppE` LitE (StringL s))
                ]
            ]
        , persistFieldSqlInstanceD False (ConT $ mkName s)
            [ sqlTypeFunD ss
            ]
        ]

-- | Automatically creates a valid 'PersistField' instance for any datatype
-- that has valid 'ToJSON' and 'FromJSON' instances. For a datatype @T@ it
-- generates instances similar to these:
--
-- @
--    instance PersistField T where
--        toPersistValue = PersistByteString . L.toStrict . encode
--        fromPersistValue = (left T.pack) . eitherDecodeStrict' <=< fromPersistValue
--    instance PersistFieldSql T where
--        sqlType _ = SqlString
-- @
derivePersistFieldJSON :: String -> Q [Dec]
derivePersistFieldJSON s = do
    ss <- [|SqlString|]
    tpv <- [|PersistText . toJsonText|]
    fpv <- [|\dt v -> do
                text <- fromPersistValue v
                let bs' = TE.encodeUtf8 text
                case eitherDecodeStrict' bs' of
                    Left e -> Left $ pack "JSON decoding error for " ++ pack dt ++ pack ": " ++ pack e ++ pack ". On Input: " ++ decodeUtf8 bs'
                    Right x -> Right x|]
    return
        [ persistFieldInstanceD False (ConT $ mkName s)
            [ FunD 'toPersistValue
                [ normalClause [] tpv
                ]
            , FunD 'fromPersistValue
                [ normalClause [] (fpv `AppE` LitE (StringL s))
                ]
            ]
        , persistFieldSqlInstanceD False (ConT $ mkName s)
            [ sqlTypeFunD ss
            ]
        ]

-- | produce code similar to the following:
--
-- @
--   instance PersistEntity e => PersistField e where
--      toPersistValue = PersistMap $ zip columNames (map toPersistValue . toPersistFields)
--      fromPersistValue (PersistMap o) =
--          let columns = HM.fromList o
--          in fromPersistValues $ map (\name ->
--            case HM.lookup name columns of
--              Just v -> v
--              Nothing -> PersistNull
--      fromPersistValue x = Left $ "Expected PersistMap, received: " ++ show x
--      sqlType _ = SqlString
-- @
persistFieldFromEntity :: MkPersistSettings -> EntityDef -> Q [Dec]
persistFieldFromEntity mps e = do
    ss <- [|SqlString|]
    obj <- [|\ent -> PersistMap $ zip (map pack columnNames) (map toPersistValue $ toPersistFields ent)|]
    fpv <- [|\x -> let columns = HM.fromList x
                    in fromPersistValues $ map
                         (\(name) ->
                            case HM.lookup (pack name) columns of
                                Just v -> v
                                Nothing -> PersistNull)
                         $ columnNames
          |]

    compose <- [|(<=<)|]
    getPersistMap' <- [|getPersistMap|]
    return
        [ persistFieldInstanceD (mpsGeneric mps) typ
            [ FunD 'toPersistValue [ normalClause [] obj ]
            , FunD 'fromPersistValue
                [ normalClause [] (InfixE (Just fpv) compose $ Just getPersistMap')
                ]
            ]
        , persistFieldSqlInstanceD (mpsGeneric mps) typ
            [ sqlTypeFunD ss
            ]
        ]
    where
      typ = genericDataType mps (entityHaskell e) backendT
      entFields = entityFields e
      columnNames  = map (unpack . unHaskellName . fieldHaskell) entFields
