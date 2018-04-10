{-# LANGUAGE Rank2Types, TypeFamilies, TemplateHaskell, KindSignatures #-}
module Data.Mouldable where

import Data.Functor.Identity
import Language.Haskell.TH hiding (cxt)

class Mouldable a where
  data Mould a (h :: * -> *) :: *
  mouldMap :: Applicative f => (forall x. h x -> f x) -> Mould a h -> f a
  remould :: a -> Mould a Identity
  mapMould :: (forall x. g x -> h x) -> Mould a g -> Mould a h

class Mouldable a => MouldableApply a where
  zipMould :: (forall x. f x -> g x -> h x) -> Mould a f -> Mould a g -> Mould a h

data MouldSettings = MouldSettings
  { conNameModifier :: Name -> Name
  , infixConNameModifier :: Name -> Name
  , fieldNameModifier :: Name -> Name
  }

defaultMouldSettings :: MouldSettings
defaultMouldSettings = MouldSettings
  { conNameModifier = mkName . ("M'"++) . nameBase
  , infixConNameModifier = mkName . (":"++) . nameBase
  , fieldNameModifier = mkName . ("m'"++) . nameBase }

declareMould :: DecsQ -> DecsQ
declareMould = declareMouldWith defaultMouldSettings

declareMouldWith :: MouldSettings -> DecsQ -> DecsQ
declareMouldWith cfg decsQ = do
  decs <- decsQ
  decs' <- traverse (transform cfg) decs
  return $ concat decs'

asTyVar :: TyVarBndr -> Type
asTyVar (PlainTV name) = VarT name
asTyVar (KindedTV name _) = VarT name

transformCon :: MouldSettings -> Name -> Con -> Con
transformCon cfg h (NormalC name xs) = NormalC (conNameModifier cfg name)
  [(b, VarT h `AppT` t) | (b, t) <- xs]
transformCon cfg h (RecC name xs) = RecC (conNameModifier cfg name)
  [(fieldNameModifier cfg v, b, VarT h `AppT` t) | (v, b, t) <- xs]
transformCon cfg h (InfixC (lb, lt) name (rb, rt)) = InfixC
    (lb, VarT h `AppT` lt)
    (infixConNameModifier cfg name)
    (rb, VarT h `AppT` rt)
transformCon cfg h (ForallC tvbs cxt con) = ForallC tvbs cxt (transformCon cfg h con)
transformCon _ _ con = error $ "Unsupported: " ++ show con

vars :: String -> [a] -> [Name]
vars p xs = [mkName (p ++ show i) | (i, _) <- zip [0 :: Int ..] xs]

con2Pat :: String -> Con -> (Pat, [Name])
con2Pat p (NormalC name xs) = (ConP name (map VarP (vars p xs)), vars p xs)
con2Pat p (RecC name xs) = (ConP name (map VarP (vars p xs)), vars p xs)
con2Pat p (InfixC _ name _) = (InfixP (VarP a) name (VarP b), [a, b]) where
  a = mkName $ p ++ "a"
  b = mkName $ p ++ "b"

conName :: Con -> Name
conName (NormalC name _) = name
conName (RecC name _) = name
conName (InfixC _ name _) = name

transform :: MouldSettings -> Dec -> Q [Dec]
transform cfg (DataD cxt name tvbs kind cons _) = do
  var <- newName "h"
  let cons' = map (transformCon cfg var) cons
  return $ concat [ pure $ DataD cxt name tvbs kind cons []
    , pure $ InstanceD Nothing [] (ConT ''Mouldable `AppT` ConT name)
      [ DataInstD [] ''Mould
          [foldl AppT (ConT name) (map asTyVar tvbs)
          , VarT var] Nothing
          cons'
          []

      , FunD 'mouldMap [Clause
        [VarP var, p]
        (NormalB $ foldl
          (\x (op, v) -> InfixE (Just x) (VarE op) (Just (VarE var `AppE` VarE v)))
          (ConE (conName con)) $ zip ('(<$>) : repeat '(<*>)) vs)
        []
        | (con, con') <- zip cons cons'
        , let (p, vs) = con2Pat "v" con']

      , FunD 'remould [Clause
        [p]
        (NormalB $ foldl
          (\x v -> AppE x (VarE 'pure `AppE` VarE v))
          (ConE (conName con')) vs)
        []
        | (con, con') <- zip cons cons'
        , let (p, vs) = con2Pat "v" con]

      , FunD 'mapMould [Clause
        [VarP var, p]
        (NormalB $ foldl
          (\x v -> AppE x (VarE var `AppE` VarE v))
          (ConE (conName con)) vs)
        []
        | con <- cons'
        , let (p, vs) = con2Pat "v" con]]
    , [InstanceD Nothing [] (ConT ''MouldableApply `AppT` ConT name)
      [ FunD 'zipMould [Clause
        [VarP var, p, q]
        (NormalB $ foldl
          (\r (x, y) -> AppE r (VarE var `AppE` VarE x `AppE` VarE y))
          (ConE (conName con)) (zip xs ys))
        []
        ]]
      | [con] <- pure cons'
      , let (p, xs) = con2Pat "p" con
      , let (q, ys) = con2Pat "q" con
      ]]
transform _ d = pure [d]
