module Lec1 where

data List (X : Set) : Set where
    <>  :  List X
    _,_ : X -> List X -> List X

zap : {S T : Set} -> List (S -> T) -> List S -> List T
zap <> xs = ?
zap (y , y') xs = ?