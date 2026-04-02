module re where

data RList (States : Set) (S : States) (S' : States) (X : Set) (f : State → X → State) : Set where
  <> : RList States S S X f
  _,_ : X → RList States S S' X f → RList States (f X s) s' X f