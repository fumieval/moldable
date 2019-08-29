{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE FlexibleInstances #-}
{-# OPTIONS_GHC -ddump-splices #-}
module TH where

import Data.Moldable

declareMold [d|
  data Foo = Foo
    { foo :: Int
    , bar :: Bool
    }
  |]

deriving instance Show (Foo Raw)

main :: IO ()
main = return ()
