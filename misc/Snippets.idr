module Schema

namespace ListHasExactlyOneElement
    data ListHasExactlyOneElement : {elem : Type} -> List elem -> Type where
        Because     : ListHasExactlyOneElement (x :: [])

    getElementFromProof : (prf : ListHasExactlyOneElement {elem} xs) -> elem
    getElementFromProof (Because {x}) = x
