{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE DataKinds #-}
{-# OPTIONS_GHC -ddump-splices #-}


import Data.Moldable

declareMold [d|
  data Foo = Foo
    { foo :: Int
    , bar :: Bool
    }
  |]

main = return ()
