{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeFamilies #-}
{-# OPTIONS_GHC -ddump-splices #-}


import Data.Mouldable

declareMould [d|
  data Foo = Foo
    { foo :: Int
    , bar :: Bool
    }
  |]

main = return ()
