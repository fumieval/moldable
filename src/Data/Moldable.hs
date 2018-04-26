{-# LANGUAGE Rank2Types, TypeFamilies, TemplateHaskell, KindSignatures #-}
module Data.Moldable where

import Data.Functor.Identity
import Data.Tagged
import Language.Haskell.TH hiding (cxt)

class Moldable a where
  data Mold a (h :: * -> *) :: *
  moldMap :: Applicative f => (forall x. h x -> f x) -> Mold a h -> f a
  remold :: a -> Mold a Identity
  traverseMold :: Applicative f => (forall x. g x -> f (h x)) -> Mold a g -> f (Mold a h)

class Moldable a => MoldableZip a where
  zipMold :: (forall x. f x -> g x -> h x) -> Mold a f -> Mold a g -> Mold a h

data MoldSettings = MoldSettings
  { conNameModifier :: Name -> Name
  , infixConNameModifier :: Name -> Name
  , fieldNameModifier :: Name -> Name
  , tagRecordFields :: Bool
  }

defaultMoldSettings :: MoldSettings
defaultMoldSettings = MoldSettings
  { conNameModifier = mkName . ("M'"++) . nameBase
  , infixConNameModifier = mkName . (":"++) . nameBase
  , fieldNameModifier = mkName . ("m'"++) . nameBase
  , tagRecordFields = True
  }

declareMold :: DecsQ -> DecsQ
declareMold = declareMoldWith defaultMoldSettings

declareMoldWith :: MoldSettings -> DecsQ -> DecsQ
declareMoldWith cfg decsQ = do
  decs <- decsQ
  decs' <- traverse (transform cfg) decs
  return $ concat decs'

asTyVar :: TyVarBndr -> Type
asTyVar (PlainTV name) = VarT name
asTyVar (KindedTV name _) = VarT name

transformCon :: MoldSettings
  -> Name -- ^ the name of the wrapper variable
  -> Con -- ^ original constructor
  -> (Con -- modified constructor
    , Name -- original constructor name
    , Name -- modified constructor name
    , Int -- number of fields
    , [Exp] -- wrap fields
    , [Exp] -- unwrap fields
    )
transformCon cfg h (NormalC name xs) =
  (NormalC name' [(b, VarT h `AppT` t) | (b, t) <- xs]
  , name, name', length xs, repeat (VarE 'id), repeat (VarE 'id))
  where
    name' = conNameModifier cfg name
transformCon cfg h (RecC name xs) = (RecC name'
  [(fieldNameModifier cfg v, b, VarT h `AppT` t')
  | (v, b, t) <- xs
  , let t' | tagRecordFields cfg = ConT ''Tagged `AppT` LitT (StrTyLit $ nameBase v) `AppT` t
           | otherwise = t
  ], name, name', length xs
  , if tagRecordFields cfg
    then repeat (ConE 'Tagged)
    else repeat (VarE 'id)
  , if tagRecordFields cfg
    then repeat (VarE 'unTagged)
    else repeat (VarE 'id)
  )
  where
    name' = conNameModifier cfg name
transformCon cfg h (InfixC (lb, lt) name (rb, rt)) = (InfixC
  (lb, VarT h `AppT` lt)
  name
  (rb, VarT h `AppT` rt)
  , name, name', 2, repeat (VarE 'id), repeat (VarE 'id))
  where
    name' = infixConNameModifier cfg name
transformCon cfg h (ForallC tvbs cxt con) =
  let (con', name, name', n, forward, backward) = transformCon cfg h con
  in (ForallC tvbs cxt con', name, name', n, forward, backward)
transformCon _ _ con = error $ "transformCon: unsupported " ++ show con

varNames :: String -> Int -> [Name]
varNames p n = [mkName (p ++ show i) | i <- [0..n - 1]]

transform :: MoldSettings -> Dec -> Q [Dec]
transform cfg (DataD cxt dataName tvbs kind cons _) = do
  var <- newName "h"
  let transformed = map (transformCon cfg var) cons
  return $ concat [ pure $ DataD cxt dataName tvbs kind cons []
    , pure $ InstanceD Nothing [] (ConT ''Moldable `AppT` ConT dataName)
      [ DataInstD [] ''Mold
          [foldl AppT (ConT dataName) (map asTyVar tvbs)
          , VarT var] Nothing
          (map (\(c,_,_,_,_,_) -> c) transformed)
          []

      , FunD 'moldMap [Clause
        [VarP var, ConP name' $ map VarP vs]
        (NormalB $ foldl
          (\x (op, v, u) -> InfixE (Just x) (VarE op) (Just $ VarE 'fmap `AppE` u `AppE` (VarE var `AppE` VarE v)))
          (ConE name) $ zip3 ('(<$>) : repeat '(<*>)) vs unwrap)
        []
        | (_, name, name', n, _, unwrap) <- transformed
        , let vs = varNames "v" n]
      , FunD 'remold [Clause
        [ConP name $ map VarP vs]
        (NormalB $ foldl
          (\x (v, w) -> AppE x (VarE 'pure `AppE` (w `AppE` VarE v)))
          (ConE name') (zip vs wrap))
        []
        | (_, name, name', n, wrap, _) <- transformed
        , let vs = varNames "v" n]
      , FunD 'traverseMold [Clause
        [VarP var, ConP name' $ map VarP vs]
        (NormalB $ foldl
          (\x (op, v) -> InfixE (Just x) (VarE op) $ Just $ VarE var `AppE` VarE v)
          (ConE name') $ zip ('(<$>) : repeat '(<*>)) vs)
        []
        | (_, _, name', n, _, _) <- transformed
        , let vs = varNames "v" n]]
    , [InstanceD Nothing [] (ConT ''MoldableZip `AppT` ConT dataName)
      [ FunD 'zipMold [Clause
        [VarP var, ConP name' $ map VarP xs, ConP name' $ map VarP ys]
        (NormalB $ foldl
          (\r (x, y) -> AppE r (VarE var `AppE` VarE x `AppE` VarE y))
          (ConE name') (zip xs ys))
        []
        ]]
      | [(_, _, name', n, _, _)] <- pure transformed
      , let xs = varNames "x" n
      , let ys = varNames "y" n
      ]]
transform _ d = pure [d]
