{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeFamilies #-}
module Data.Moldable (Moldable(..)
  , Raw
  , Ann
  , Shroud
  , declareMold
  , Wrap(..)
  , rewrap
  , rewrapF
  ) where

import Language.Haskell.TH hiding (cxt)
import qualified Data.Kind as K
import Data.Tagged
import GHC.TypeLits
import Unsafe.Coerce

data Raw
data Ann (f :: Symbol -> K.Type -> K.Type)

type family Shroud switch name a where
  Shroud Raw _ a = a
  Shroud (Ann f) name a = f name a

-- | Turn a conventional wrapper into an annotated wrapper
data Wrap h name a = Wrap { unWrap :: h a }

-- | Modify the content of 'Wrap'.
rewrap :: (forall x. f x -> g x) -> Wrap f k a -> Wrap g k a
rewrap f = Wrap . f . unWrap
{-# INLINE rewrap #-}

-- | Modify the content of 'Wrap' over a functor.
rewrapF :: Functor t => (forall x. f x -> t (g x)) -> Wrap f k a -> t (Wrap g k a)
rewrapF f = fmap Wrap . f . unWrap
{-# INLINE rewrapF #-}

class Moldable m where
  annotateMold :: m Raw -> m (Ann Tagged)
  unannotateMold :: m (Ann Tagged) -> m Raw
  traverseMold :: Applicative f => (forall k x. KnownSymbol k => g k x -> f (h k x)) -> m (Ann g) -> f (m (Ann h))
  traverseMold_ :: Applicative f => (forall k x. KnownSymbol k => g k x -> f r) -> m (Ann g) -> f ()
  zipMold :: (forall k x. KnownSymbol k => f k x -> g k x -> h k x) -> m (Ann f) -> m (Ann g) -> m (Ann h)
  zipMoldA :: Applicative t => (forall k x. KnownSymbol k => f k x -> g k x -> t (h k x)) -> m (Ann f) -> m (Ann g) -> t (m (Ann h))
  zipMoldA_ :: Applicative t => (forall k x. KnownSymbol k => f k x -> g k x -> t r) -> m (Ann f) -> m (Ann g) -> t ()

declareMold :: DecsQ -> DecsQ
declareMold decsQ = do
  decs <- decsQ
  decs' <- traverse go decs
  return $ concat decs'
  where
    go (DataD _ dataName tvbs _ cons drv) = do
      var <- newName "sw"
      let transformed = map (transformCon var) cons
      decs <- deriveMoldlike (ConT dataName) transformed
      return $ DataD [] dataName
        (tvbs ++ [PlainTV var])
        Nothing
        (map (\(c,_,_) -> c) transformed)
        drv
        : decs
    go d = pure [d]

type ConInfo = (Con -- modified constructor
  , Name -- original constructor name
  , Int -- number of fields
  )

transformCon :: Name -- ^ switch variable
  -> Con -- ^ original constructor
  -> ConInfo
transformCon switchName (RecC name xs) = (RecC name
  [(v, b, ConT ''Shroud
    `AppT` VarT switchName
    `AppT` LitT (StrTyLit $ nameBase v)
    `AppT` t)
  | (v, b, t) <- xs
  ], name, length xs
  )
transformCon var (ForallC tvbs cxt con) =
  let (con', name, n) = transformCon var con
  in (ForallC tvbs cxt con', name, n)
transformCon _ con = error $ "transformCon: unsupported " ++ show con

varNames :: String -> Int -> [Name]
varNames p n = [mkName (p ++ show i) | i <- [0..n - 1]]

deriveMoldlike :: Type -> [ConInfo] -> DecsQ
deriveMoldlike moldTy transformed = do
  var <- newName "t"
  return $ pure $ InstanceD Nothing [] (ConT ''Moldable `AppT` moldTy) $
      [ ValD (VarP 'annotateMold) (NormalB $ VarE 'unsafeCoerce) []
      , PragmaD $ InlineP 'annotateMold Inline FunLike AllPhases
      , ValD (VarP 'unannotateMold) (NormalB $ VarE 'unsafeCoerce) []
      , PragmaD $ InlineP 'unannotateMold Inline FunLike AllPhases
      , FunD 'traverseMold [Clause
        [VarP var, ConP name' $ map VarP vs]
        (NormalB $ foldl
          (\x (op, v) -> InfixE (Just x) (VarE op) $ Just $ VarE var `AppE` VarE v)
          (ConE name') $ zip ('(<$>) : repeat '(<*>)) vs)
        []
        | (_, name', n) <- transformed
        , let vs = varNames "v" n]
    , PragmaD $ InlineP 'traverseMold Inline FunLike AllPhases
    , FunD 'traverseMold_ [Clause
        [VarP var, ConP name' $ map VarP vs]
        (NormalB $ foldr
          (\v x -> InfixE (Just $ VarE var `AppE` VarE v) (VarE '(*>)) $ Just x)
          (VarE 'pure `AppE` TupE []) vs)
        []
        | (_, name', n) <- transformed
        , let vs = varNames "v" n]
    , PragmaD $ InlineP 'traverseMold_ Inline FunLike AllPhases
    ] ++ concat [[FunD 'zipMold [Clause
        [VarP var, ConP name' $ map VarP xs, ConP name' $ map VarP ys]
        (NormalB $ foldl
          (\r (x, y) -> AppE r (VarE var `AppE` VarE x `AppE` VarE y))
          (ConE name') (zip xs ys))
        []
        ]
    , PragmaD $ InlineP 'zipMold Inline FunLike AllPhases
    , FunD 'zipMoldA [Clause
      [VarP var, ConP name' $ map VarP xs, ConP name' $ map VarP ys]
      (NormalB $ foldl
        (\r (op, x, y) -> InfixE (Just r) (VarE op) $ Just $ VarE var `AppE` VarE x `AppE` VarE y)
        (ConE name') (zip3 ('(<$>) : repeat '(<*>)) xs ys))
      []
      ]
    , PragmaD $ InlineP 'zipMoldA Inline FunLike AllPhases
    , FunD 'zipMoldA_ [Clause
      [VarP var, ConP name' $ map VarP xs, ConP name' $ map VarP ys]
      (NormalB $ foldr
        (\(x, y) r -> InfixE (Just $ VarE var `AppE` VarE x `AppE` VarE y) (VarE '(*>)) $ Just r)
        (VarE 'pure `AppE` TupE []) (zip xs ys))
      []
      ]
    , PragmaD $ InlineP 'zipMoldA_ Inline FunLike AllPhases
    ]
    | [(_, name', n)] <- pure transformed
    , let xs = varNames "x" n
    , let ys = varNames "y" n
    ]
