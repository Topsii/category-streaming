# category-streaming

### Categories

- https://hackage.haskell.org/package/data-category
- https://hackage.haskell.org/package/constrained-categories
- https://hackage.haskell.org/package/categories
- https://hackage.haskell.org/package/hask

### Functor/Applicative/Monad/Traversable etc. for a nonstandard category

| Package                                                                                                                                                                                                                                                | Naming                                                                      | Source Category                                                                                              | Target Category       |
|--------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------|-----------------------------------------------------------------------------|--------------------------------------------------------------------------------------------------------------|-----------------------|
| [barbies](https://hackage.haskell.org/package/barbies/docs/Data-Functor-Barbie.html)                                                                                                                                                                   | suffix B                                                                    | NaturalTransformation                                                                                        | (->)                  |
| [conkin](https://hackage.haskell.org/package/conkin)                                                                                                                                                                                                   | collides with standard classes                                              | NaturalTransformation                                                                                        | (->)                  |
| [Functor Functors](https://www.benjamin.pizza/posts/2017-12-15-functor-functors.html)                                                                                                                                                                  | prefix F                                                                    | NaturalTransformation                                                                                        | (->)                  |
| [ten](https://hackage.haskell.org/package/ten)                                                                                                                                                                                                         | suffix 10                                                                   | NaturalTransformation                                                                                        | (->)                  |
| [rank2classes](https://hackage.haskell.org/package/rank2classes)                                                                                                                                                                                       | collides with standard classes                                              | NaturalTransformation                                                                                        | (->)                  |
| [yaya](https://hackage-content.haskell.org/package/yaya/docs/Yaya-Functor.html#t:DFunctor)                                                                                                                                                             | prefix D                                                                    | NaturalTransformation                                                                                        | (->)                  |
| [barbies](https://hackage.haskell.org/package/barbies/docs/Data-Functor-Transformer.html)                                                                                                                                                              | suffix T                                                                    | NaturalTransformation                                                                                        | NaturalTransformation |
| [index-core](https://hackage.haskell.org/package/index-core/docs/Control-IMonad-Core.html)                                                                                                                                                             | prefix I                                                                    | NaturalTransformation                                                                                        | NaturalTransformation |
| [functor-combinators](https://hackage-content.haskell.org/package/functor-combinators) <br> [yaya](https://hackage-content.haskell.org/package/yaya/docs/Yaya-Functor.html#t:HFunctor)                                                                 | prefix H                                                                    | NaturalTransformation                                                                                        | NaturalTransformation |
| [membership](https://hackage.haskell.org/package/membership/docs/Type-Membership-HList.html#v:htraverse)                                                                                                                                               | (prefix h for specialized case **h**eterogenous list)                       | NaturalTransformation                                                                                        | NaturalTransformation |
| [mmorph](https://hackage.haskell.org/package/mmorph) <br> [transformers](https://hackage-content.haskell.org/package/transformers/docs/Control-Monad-Trans-Class.html)                                                                                 | prefix M                                                                    | MonadMorphism                                                                                                | MonadMorphism         |
| [indexed-traversable](https://hackage.haskell.org/package/indexed-traversable) <br> [witherable](https://hackage.haskell.org/package/witherable) <br> [~~semialign?~~](https://hackage.haskell.org/package/semialign/docs/Data-Semialign-Indexed.html) | suffix WithIndex                                                            | [(Indexed i)](https://hackage-content.haskell.org/package/lens/docs/Control-Lens-Combinators.html#t:Indexed) | (->)                  |
| [ten](https://hackage.haskell.org/package/ten)                                                                                                                                                                                                         | suffix 10WithIndex                                                          | Index10 f a -> m a -> n a                                                                                    | (->)                  |
| [membership](https://hackage.haskell.org/package/membership/docs/Type-Membership-HList.html)                                                                                                                                                           | (prefix h for specialized case **h**eterogenous list) <br> suffix WithIndex | Membership xs x -> g x -> f (h x)                                                                            | NaturalTransformation |
| [witherable](https://hackage.haskell.org/package/witherable)                                                                                                                                                                                           | Functor ~ Filterable <br> Traversable ~ Witherable                          | (Star Maybe)                                                                                                 | (->)                  |




### Desugars into (cartesian) category, related to the paper "compiling to categories" by Conal Elliot

- https://github.com/compiling-to-categories/concat/blob/master/classes/src/ConCat/Category.hs
- https://hackage.haskell.org/package/overloaded-0.3.1/docs/Overloaded-Categories.html
- https://github.com/con-kitty/categorifier (https://bobkonf.de/2022/pfeil.html)
- https://hackage.haskell.org/package/linear-smc (https://assert-false.science/arnaud/papers/Evaluating%20Linear%20Functions%20to%20Symmetric%20Monoidal%20Categories.pdf)


### Profunctors as an alternative to Categories

- https://stackoverflow.com/questions/53777851/examples-of-cartesian-profunctor
  https://hackage-content.haskell.org/package/lens
- https://beuke.org/profunctor-optics/#category-theoretic-foundations-of-profunctor-optics
  https://oleg.fi/gists/posts/2017-04-18-glassery.html
- https://github.com/sjoerdvisscher/proarrow/
  https://sjoerdvisscher.github.io/proarrow/index.html