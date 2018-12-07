inductive color : Type
| red : color
| black : color

export color (red black)

def color.repr : color → string
| red   := "R"
| black := "B"

instance : has_repr (color) := ⟨color.repr⟩

namespace rb_tree
/- Leaf nodes do not hold values. They are considered to be black. 
   The following implementation represents sets. -/

inductive tree : Type
| empty {} : tree
| node (c : color) (l : tree) (x : ℕ) (r : tree) : tree

export tree (empty node)

def tree.repr : tree → string
| empty          := "NIL"
| (node c l x r) := "(" ++ tree.repr l ++ " [" ++ repr x ++ ", " ++ repr c ++ "] " ++ tree.repr r ++ ")"

instance : has_repr (tree) := ⟨tree.repr⟩

def member (x : ℕ) : tree → bool
| empty          := ff
| (node _ l y r) := 
    if      x < y then member l
    else if x > y then member r
    else               tt

def make_black : tree → tree
| (node _ l x r) := node black l x r
| empty          := empty

def balance : color → tree → ℕ → tree → tree
| black (node red (node red l x r) y r') z r'' := 
    node red (node black l x r) y (node black r' z r'')
| black (node red l x (node red l' y r)) z r' :=
   node red (node black l x l') y (node black r z r')
| black l x (node red (node red l' y r) z r') :=
   node red (node black l x l') y (node black r z r')
| black l x (node red l' y (node red l'' z r)) :=
   node red (node black l x l') y (node black l'' z r)
| c l x r := node c l x r

def insert' (x : ℕ) : tree → tree
| empty            := node red empty x empty
| t@(node c l y r) := 
    if      x < y then balance c (insert' l) y r
    else if x > y then balance c l y (insert' r)
    else               t

def insert (x : ℕ) (t : tree) : tree 
:= make_black (insert' x t)

#eval insert 5 (insert 0 (insert 1 (insert 2 empty)))

/- 
    Invariant 0. For any (node color l x r), 
                 x is greater than any element in l 
                 and less than any element in r.
    Invariant 1. No red node has a red parent.
    Invariant 2. Every path from the root to an empty node contains the same number
                 of black nodes. 
-/

end rb_tree