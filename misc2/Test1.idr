module Language

%default total

namespace ListHasExactlyOneElement
    data ListHasExactlyOneElement : (a : Type) -> List a -> Type where
        Because     : ListHasExactlyOneElement ty (x :: [])

getElementFromProof : (prf : ListHasExactlyOneElement ty xs) -> ty
getElementFromProof (Because {x}) = x
