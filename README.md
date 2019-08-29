![logo](https://github.com/fumieval/moldable/blob/master/artwork/logo-256px.png?raw=true)

```haskell
declareMold [d|
  data Foo = Foo
    { foo :: Int
    , bar :: Bool
    }
```

The declaration above instead creates a following datatype:

```haskell
data Foo s = Foo
  { foo :: Shroud s "foo" Int
  , bar :: Shroud s "bar" Bool
  }
```

`Shroud` is a type family that wraps a type depending on the switch type.
`Foo Raw` is equivalent to the original declaration and `Foo (Ann f)` wraps each
field by `f`.

```haskell
type family Shroud switch name a where
  Shroud Raw _ a = a
  Shroud (Ann f) name a = f name a
```

The datatype is an instance of the `Moldable` class:

```haskell
class Moldable m where
  annotateMold :: m Raw -> m (Ann Tagged)
  unannotateMold :: m (Ann Tagged) -> m Raw
  traverseMold :: Applicative f => (forall k x. KnownSymbol k => g k x -> f (h k x)) -> m (Ann g) -> f (m (Ann h))
  traverseMold_ :: Applicative f => (forall k x. KnownSymbol k => g k x -> f r) -> m (Ann g) -> f ()
  zipMold :: (forall k x. KnownSymbol k => f k x -> g k x -> h k x) -> m (Ann f) -> m (Ann g) -> m (Ann h)
  zipMoldA :: Applicative t => (forall k x. KnownSymbol k => f k x -> g k x -> t (h k x)) -> m (Ann f) -> m (Ann g) -> t (m (Ann h))
  zipMoldA_ :: Applicative t => (forall k x. KnownSymbol k => f k x -> g k x -> t r) -> m (Ann f) -> m (Ann g) -> t ()
```

`Wrap` allows you to use `Type -> Type` wrappers.

```haskell
data Wrap h name a = Wrap { unWrap :: h a }

rewrap :: (forall x. f x -> g x) -> Wrap f k a -> Wrap g k a
rewrapF :: Functor t => (forall x. f x -> t (g x)) -> Wrap f k a -> t (Wrap g k a)
```
