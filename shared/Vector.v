Require Import Coq.Lists.List.

Axiom vector : Type -> Type.
Axiom length : forall {A}, vector A -> nat.
Axiom get : forall {A} (v:vector A) (i:nat), (i < length v) -> A.
Axiom of_list : forall {A}, list A -> vector A.

Axiom get_of_list : 
  forall A (l:list A) i (H:i < length (of_list l)), 
    nth_error l i = Some (@get _ (of_list l) i H).
Axiom length_of_list : 
  forall A (l:list A), length (of_list l) = List.length l.

Extract Constant vector "'a" => "'a array".
Extract Constant length => "fun v -> Big.of_int (Array.length v)".
Extract Constant get => "fun v i -> Array.unsafe_get v (Big.to_int i)".
Extract Inlined Constant of_list => "Array.of_list".
