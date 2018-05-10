module Language

data Liar : Type where
    MkLiar : Not Liar -> Liar  

honest : Not Liar 
honest l@(MkLiar f) = f l
-- honest l@(MkLiar p) = p l 

broken : Void 
broken = honest $ MkLiar honest 
