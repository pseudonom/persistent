{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE DefaultSignatures #-}
{-# LANGUAGE Rank2Types #-}
{-# OPTIONS_GHC -fno-warn-orphans #-}
module Database.Persist.Sql.Orphan.PersistStore
  ( withRawQuery
  , BackendKey(..)
  , toSqlKey
  , fromSqlKey
  , getFieldName
  , getTableName
  , tableDBName
  , fieldDBName
  ) where

import Database.Persist
import Database.Persist.Sql.Types
import Database.Persist.Sql.Raw
import Database.Persist.Sql.Util (dbIdColumns, keyAndEntityColumnNames)
import qualified Data.Conduit as C
import qualified Data.Conduit.List as CL
import qualified Data.Text as T
import Data.Text (Text, unpack)
import Data.Monoid (mappend, (<>))
import Control.Monad.IO.Class
import Data.ByteString.Char8 (readInteger)
import Data.Maybe (isJust)
import Data.List (find)
import Control.Monad.Trans.Reader (ReaderT, ask)
import Data.Acquire (with)
import Data.Int (Int64)
import Web.PathPieces (PathPiece)
import Web.HttpApiData (ToHttpApiData, FromHttpApiData)
import Database.Persist.Sql.Class (PersistFieldSql)
import qualified Data.Aeson as A
import Control.Exception.Lifted (throwIO)

withRawQuery :: (MonadIO m, HasPersistBackend backend SqlBackend)
             => Text
             -> [PersistValue]
             -> C.Sink [PersistValue] IO a
             -> ReaderT backend m a
withRawQuery sql vals sink = do
    srcRes <- rawQueryRes sql vals
    liftIO $ with srcRes (C.$$ sink)

toSqlKey :: ToBackendKey SqlBackend record => Int64 -> Key record
toSqlKey = fromBackendKey . SqlBackendKey

fromSqlKey :: ToBackendKey SqlBackend record => Key record -> Int64
fromSqlKey = unSqlBackendKey . toBackendKey

whereStmtForKey :: PersistEntity record => SqlBackend -> Key record -> Text
whereStmtForKey conn k =
    T.intercalate " AND "
  $ map (<> "=? ")
  $ dbIdColumns conn entDef
  where
    entDef = entityDef $ dummyFromKey k


-- | get the SQL string for the table that a PeristEntity represents
-- Useful for raw SQL queries
--
-- Your backend may provide a more convenient tableName function
-- which does not operate in a Monad
getTableName :: forall record backend m.
             ( PersistEntity record
             , PersistEntityBackend record ~ backend
             , HasPersistBackend backend SqlBackend
             , Monad m
             ) => record -> ReaderT backend m Text
getTableName rec = do
    conn <- persistBackend <$> ask
    return $ connEscapeName conn $ tableDBName rec

-- | useful for a backend to implement tableName by adding escaping
tableDBName
    :: ( PersistEntity record
       , PersistEntityBackend record ~ backend
       , HasPersistBackend backend SqlBackend
       )
    => record -> DBName
tableDBName rec = entityDB $ entityDef (Just rec)

-- | get the SQL string for the field that an EntityField represents
-- Useful for raw SQL queries
--
-- Your backend may provide a more convenient fieldName function
-- which does not operate in a Monad
getFieldName :: forall record backend typ m.
             ( PersistEntity record
             , HasPersistBackend backend SqlBackend
             , PersistEntityBackend record ~ backend
             , Monad m
             )
             => EntityField record typ -> ReaderT backend m Text
getFieldName rec = do
    conn <- persistBackend <$> ask
    return $ connEscapeName conn $ fieldDBName rec

-- | useful for a backend to implement fieldName by adding escaping
fieldDBName :: forall record typ. (PersistEntity record) => EntityField record typ -> DBName
fieldDBName = fieldDB . persistFieldDef


instance PersistCore SqlBackend where
    newtype BackendKey SqlBackend = SqlBackendKey { unSqlBackendKey :: Int64 }
        deriving (Show, Read, Eq, Ord, Num, Integral, PersistField, PersistFieldSql, PathPiece, ToHttpApiData, FromHttpApiData, Real, Enum, Bounded, A.ToJSON, A.FromJSON)
instance PersistCore SqlReadBackend where
    newtype BackendKey SqlReadBackend = SqlReadBackendKey { unSqlReadBackendKey :: Int64 }
        deriving (Show, Read, Eq, Ord, Num, Integral, PersistField, PersistFieldSql, PathPiece, ToHttpApiData, FromHttpApiData, Real, Enum, Bounded, A.ToJSON, A.FromJSON)
instance PersistCore SqlWriteBackend where
    newtype BackendKey SqlWriteBackend = SqlWriteBackendKey { unSqlWriteBackendKey :: Int64 }
        deriving (Show, Read, Eq, Ord, Num, Integral, PersistField, PersistFieldSql, PathPiece, ToHttpApiData, FromHttpApiData, Real, Enum, Bounded, A.ToJSON, A.FromJSON)


instance PersistStoreWrite SqlBackend where
  insert = insertCore
  insertMany = insertManyCore
  insertMany_ = insertMany_Core
  insertKey = insertKeyCore
  repsert = repsertCore
  replace = replaceCore
  delete = deleteCore
  update = updateCore
instance PersistStoreWrite SqlWriteBackend where
  insert = insertCore
  insertMany = insertManyCore
  insertMany_ = insertMany_Core
  insertKey = insertKeyCore
  repsert = repsertCore
  replace = replaceCore
  delete = deleteCore
  update = updateCore

updateCore
  :: (MonadIO m, PersistEntity val, backend ~ PersistEntityBackend val, HasPersistBackend backend SqlBackend)
  => Key val -> [Update val] -> ReaderT backend m ()
updateCore _ [] = return ()
updateCore k upds = do
    conn <- persistBackend <$> ask
    let go'' n Assign = n <> "=?"
        go'' n Add = T.concat [n, "=", n, "+?"]
        go'' n Subtract = T.concat [n, "=", n, "-?"]
        go'' n Multiply = T.concat [n, "=", n, "*?"]
        go'' n Divide = T.concat [n, "=", n, "/?"]
        go'' _ (BackendSpecificUpdate up) = error $ T.unpack $ "BackendSpecificUpdate" `mappend` up `mappend` "not supported"
    let go' (x, pu) = go'' (connEscapeName conn x) pu
    let wher = whereStmtForKey conn k
    let sql = T.concat
            [ "UPDATE "
            , connEscapeName conn $ tableDBName $ recordTypeFromKey k
            , " SET "
            , T.intercalate "," $ map (go' . go) upds
            , " WHERE "
            , wher
            ]
    rawExecute sql $
        map updatePersistValue upds `mappend` keyToValues k
  where
    go x = (fieldDB $ updateFieldDef x, updateUpdate x)

insertCore
    :: (MonadIO m, PersistEntity val, backend ~ PersistEntityBackend val, HasPersistBackend backend SqlBackend)
    => val -> ReaderT backend m (Key val)
insertCore val = do
    conn <- persistBackend <$> ask
    let esql = connInsertSql conn t vals
    key <-
        case esql of
            ISRSingle sql -> withRawQuery sql vals $ do
                x <- CL.head
                case x of
                    Just [PersistInt64 i] -> case keyFromValues [PersistInt64 i] of
                        Left err -> error $ "SQL insert: keyFromValues: PersistInt64 " `mappend` show i `mappend` " " `mappend` unpack err
                        Right k -> return k
                    Nothing -> error $ "SQL insert did not return a result giving the generated ID"
                    Just vals' -> case keyFromValues vals' of
                        Left _ -> error $ "Invalid result from a SQL insert, got: " ++ show vals'
                        Right k -> return k

            ISRInsertGet sql1 sql2 -> do
                rawExecute sql1 vals
                withRawQuery sql2 [] $ do
                    mm <- CL.head
                    let m = maybe
                              (Left $ "No results from ISRInsertGet: " `mappend` tshow (sql1, sql2))
                              Right mm

                    -- TODO: figure out something better for MySQL
                    let convert x =
                            case x of
                                [PersistByteString i] -> case readInteger i of -- mssql
                                                        Just (ret,"") -> [PersistInt64 $ fromIntegral ret]
                                                        _ -> x
                                _ -> x
                        -- Yes, it's just <|>. Older bases don't have the
                        -- instance for Either.
                        onLeft Left{} x = x
                        onLeft x _ = x

                    case m >>= (\x -> keyFromValues x `onLeft` keyFromValues (convert x)) of
                        Right k -> return k
                        Left err -> throw $ "ISRInsertGet: keyFromValues failed: " `mappend` err
            ISRManyKeys sql fs -> do
                rawExecute sql vals
                case entityPrimary t of
                   Nothing -> error $ "ISRManyKeys is used when Primary is defined " ++ show sql
                   Just pdef ->
                        let pks = map fieldHaskell $ compositeFields pdef
                            keyvals = map snd $ filter (\(a, _) -> let ret=isJust (find (== a) pks) in ret) $ zip (map fieldHaskell $ entityFields t) fs
                        in  case keyFromValues keyvals of
                                Right k -> return k
                                Left e  -> error $ "ISRManyKeys: unexpected keyvals result: " `mappend` unpack e

    return key
  where
    tshow :: Show a => a -> Text
    tshow = T.pack . show
    throw = liftIO . throwIO . userError . T.unpack
    t = entityDef $ Just val
    vals = map toPersistValue $ toPersistFields val

insertManyCore
    :: (MonadIO m, PersistEntity val, PersistEntityBackend val ~ backend, HasPersistBackend backend SqlBackend)
    => [val] -> ReaderT backend m [Key val]
insertManyCore [] = return []
insertManyCore vals = do
    conn <- persistBackend <$> ask

    case connInsertManySql conn of
        Nothing -> mapM insertCore vals
        Just insertManyFn ->
            case insertManyFn ent valss of
                ISRSingle sql -> rawSql sql (concat valss)
                _ -> error "ISRSingle is expected from the connInsertManySql function"
            where
                ent = entityDef vals
                valss = map (map toPersistValue . toPersistFields) vals


insertMany_Core
    :: (MonadIO m, PersistEntity val, PersistEntityBackend val ~ backend, HasPersistBackend backend SqlBackend)
    => [val] -> ReaderT backend m ()
insertMany_Core [] = return ()
insertMany_Core vals = do
    conn <- persistBackend <$> ask
    let sql = T.concat
            [ "INSERT INTO "
            , connEscapeName conn (entityDB t)
            , "("
            , T.intercalate "," $ map (connEscapeName conn . fieldDB) $ entityFields t
            , ") VALUES ("
            , T.intercalate "),(" $ replicate (length valss) $ T.intercalate "," $ map (const "?") (entityFields t)
            , ")"
            ]
    rawExecute sql (concat valss)
  where
    t = entityDef vals
    valss = map (map toPersistValue . toPersistFields) vals

replaceCore
    :: (MonadIO m, HasPersistBackend backend SqlBackend, PersistEntityBackend val ~ backend, PersistEntity val)
    => Key val -> val -> ReaderT backend m ()
replaceCore k val = do
    conn <- persistBackend <$> ask
    let t = entityDef $ Just val
    let wher = whereStmtForKey conn k
    let sql = T.concat
            [ "UPDATE "
            , connEscapeName conn (entityDB t)
            , " SET "
            , T.intercalate "," (map (go conn . fieldDB) $ entityFields t)
            , " WHERE "
            , wher
            ]
        vals = map toPersistValue (toPersistFields val) `mappend` keyToValues k
    rawExecute sql vals
  where
    go conn x = connEscapeName conn x `T.append` "=?"

insertKeyCore
  :: (MonadIO m, PersistEntity val, PersistEntityBackend val ~ backend, HasPersistBackend backend SqlBackend)
  => Key val -> val -> ReaderT backend m ()
insertKeyCore = insrepHelper "INSERT"

repsertCore
    :: (MonadIO m, HasPersistBackend backend SqlBackend, PersistEntityBackend val ~ backend, PersistEntity val)
    => Key val -> val -> ReaderT backend m ()
repsertCore key value = do
    mExisting <- getCore key
    case mExisting of
      Nothing -> insertKeyCore key value
      Just _ -> replaceCore key value

deleteCore
    :: (MonadIO m, HasPersistBackend backend SqlBackend, PersistEntityBackend val ~ backend, PersistEntity val)
    => Key val -> ReaderT backend m ()
deleteCore k = do
    conn <- persistBackend <$> ask
    rawExecute (sql conn) (keyToValues k)
  where
    wher conn = whereStmtForKey conn k
    sql conn = T.concat
        [ "DELETE FROM "
        , connEscapeName conn $ tableDBName $ recordTypeFromKey k
        , " WHERE "
        , wher conn
        ]

instance PersistStoreRead SqlBackend where
    get = getCore
instance PersistStoreRead SqlReadBackend where
    get = getCore
instance PersistStoreRead SqlWriteBackend where
    get = getCore

getCore
  :: (Show (Key val), MonadIO m, PersistEntity val, PersistEntityBackend val ~ backend, HasPersistBackend backend SqlBackend)
  => Key val -> ReaderT backend m (Maybe val)
getCore k = do
        conn <- persistBackend <$> ask
        let t = entityDef $ dummyFromKey k
        let cols = T.intercalate ","
                 $ map (connEscapeName conn . fieldDB) $ entityFields t
            noColumns :: Bool
            noColumns = null $ entityFields t
        let wher = whereStmtForKey conn k
        let sql = T.concat
                [ "SELECT "
                , if noColumns then "*" else cols
                , " FROM "
                , connEscapeName conn $ entityDB t
                , " WHERE "
                , wher
                ]
        withRawQuery sql (keyToValues k) $ do
            res <- CL.head
            case res of
                Nothing -> return Nothing
                Just vals ->
                    case fromPersistValues $ if noColumns then [] else vals of
                        Left e -> error $ "get " ++ show k ++ ": " ++ unpack e
                        Right v -> return $ Just v

dummyFromKey :: Key record -> Maybe record
dummyFromKey = Just . recordTypeFromKey

recordTypeFromKey :: Key record -> record
recordTypeFromKey _ = error "dummyFromKey"

insrepHelper :: (MonadIO m, PersistEntity val, PersistEntityBackend val ~ backend, HasPersistBackend backend SqlBackend)
             => Text
             -> Key val
             -> val
             -> ReaderT backend m ()
insrepHelper command k record = do
    conn <- persistBackend <$> ask
    let columnNames = keyAndEntityColumnNames entDef conn
    rawExecute (sql conn columnNames) vals
  where
    entDef = entityDef $ Just record
    sql conn columnNames = T.concat
        [ command
        , " INTO "
        , connEscapeName conn (entityDB entDef)
        , "("
        , T.intercalate "," columnNames
        , ") VALUES("
        , T.intercalate "," (map (const "?") columnNames)
        , ")"
        ]
    vals = entityValues (Entity k record)

updateFieldDef :: PersistEntity v => Update v -> FieldDef
updateFieldDef (Update f _ _) = persistFieldDef f
updateFieldDef (BackendUpdate {}) = error "updateFieldDef did not expect BackendUpdate"

updatePersistValue :: Update v -> PersistValue
updatePersistValue (Update _ v _) = toPersistValue v
updatePersistValue (BackendUpdate {}) = error "updatePersistValue did not expect BackendUpdate"
