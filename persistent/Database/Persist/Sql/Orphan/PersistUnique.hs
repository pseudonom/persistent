{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE FlexibleContexts #-}
{-# OPTIONS_GHC -fno-warn-orphans #-}
module Database.Persist.Sql.Orphan.PersistUnique () where

import Control.Exception (throwIO)
import Control.Monad.IO.Class (liftIO, MonadIO)
import Control.Monad.Trans.Reader (ReaderT)
import Database.Persist
import Database.Persist.Sql.Types
import Database.Persist.Sql.Raw
import Database.Persist.Sql.Orphan.PersistStore (withRawQuery)
import Database.Persist.Sql.Util (dbColumns, parseEntityValues)
import qualified Data.Text as T
import Data.Monoid (mappend)
import qualified Data.Conduit.List as CL
import Control.Monad.Trans.Reader (ask)

instance PersistUniqueWrite SqlBackend where
  deleteBy = deleteByCore
instance PersistUniqueWrite SqlWriteBackend where
  deleteBy = deleteByCore

deleteByCore
    :: (MonadIO m, PersistEntity val, PersistEntityBackend val ~ backend, HasPersistBackend backend SqlBackend)
    => Unique val -> ReaderT backend m ()
deleteByCore uniq = do
    conn <- persistBackend <$> ask
    let sql' = sql conn
        vals = persistUniqueToValues uniq
    rawExecute sql' vals
  where
    t = entityDef $ dummyFromUnique uniq
    go = map snd . persistUniqueToFieldNames
    go' conn x = connEscapeName conn x `mappend` "=?"
    sql conn = T.concat
        [ "DELETE FROM "
        , connEscapeName conn $ entityDB t
        , " WHERE "
        , T.intercalate " AND " $ map (go' conn) $ go uniq
        ]

instance PersistUniqueRead SqlBackend where
  getBy = getByCore
instance PersistUniqueRead SqlWriteBackend where
  getBy = getByCore
instance PersistUniqueRead SqlReadBackend where
  getBy = getByCore

getByCore
    :: (MonadIO m, PersistEntity val, HasPersistBackend backend SqlBackend, PersistEntityBackend val ~ backend)
    => Unique val -> ReaderT backend m (Maybe (Entity val))
getByCore uniq = do
    conn <- persistBackend <$> ask
    let sql = T.concat
            [ "SELECT "
            , T.intercalate "," $ dbColumns conn t
            , " FROM "
            , connEscapeName conn $ entityDB t
            , " WHERE "
            , sqlClause conn
            ]
        uvals = persistUniqueToValues uniq
    withRawQuery sql uvals $ do
        row <- CL.head
        case row of
            Nothing -> return Nothing
            Just [] -> error "getBy: empty row"
            Just vals -> case parseEntityValues t vals of
                Left err -> liftIO $ throwIO $ PersistMarshalError err
                Right r -> return $ Just r
  where
    sqlClause conn =
        T.intercalate " AND " $ map (go conn) $ toFieldNames' uniq
    go conn x = connEscapeName conn x `mappend` "=?"
    t = entityDef $ dummyFromUnique uniq
    toFieldNames' = map snd . persistUniqueToFieldNames

dummyFromUnique :: Unique v -> Maybe v
dummyFromUnique _ = Nothing
