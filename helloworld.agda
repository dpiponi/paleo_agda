module helloworld where

open import IO.Primitive using (IO; putStrLn)
open import Data.String using (toCostring; String)
open import Data.Char using (Char)
open import Foreign.Haskell using (fromColist; Colist; Unit)
open import Function

fromString = fromColist ∘ toCostring

main : IO Unit
main = putStrLn (fromString "Hello, World!")