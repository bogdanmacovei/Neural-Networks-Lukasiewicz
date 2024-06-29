section Lukasiewicz

  section Set
    inductive Set (α : Type) where
    | nil : Set α
    | cons : α → Set α → Set α
    deriving Repr

    def Set.mem {α : Type} (a : α) : Set α → Prop
    | Set.nil => false
    | (Set.cons b l) => a = b ∨ Set.mem a l

    notation x " ∈₁ " xs => Set.mem x xs

    theorem Set.mem_cons_of_mem (α : Type) {a b : α} {l : Set α} (h : a ∈₁ l)
      : a ∈₁ (Set.cons b l) := by
        exact Or.inr h

    theorem Set.mem_cons_self {α : Type} (a : α) (l : Set α)
      : a ∈₁ Set.cons a l := Or.inl rfl

    theorem Set.mem_nil {α : Type} (a : α) : ¬ (Set.mem a Set.nil) := by
      intro h
      trivial

    notation "∅₁" => Set.nil
    notation x "::" xs => Set.cons x xs

    def Set.append {α : Type} : Set α → Set α → Set α := fun l₁ ys =>
      match l₁ with
    | Set.nil => ys
    | (Set.cons x xs) => Set.cons x (Set.append xs ys)

    notation xs "++" ys => Set.append xs ys
  end Set

  section MVAlgebra

    structure Monoid (α : Type) :=
      (add : α → α → α)
      (zero : α)
      (zero_add : ∀ a : α, add zero a = a)
      (add_zero : ∀ a : α, add a zero = a)
      (add_assoc : ∀ a b c : α, add (add a b) c = add a (add b c))

    structure AbelianMonoid (α : Type) extends Monoid α :=
      (add_comm : ∀ a b : α, add a b = add b a)

    structure MV (α : Type) extends AbelianMonoid α :=
      (neg : α → α)
      (mul : Float → α → α)
      (diff : α → α → α := fun x y => neg (add (neg x) (neg y)))
      (MV₂ : ∀ x : α, neg (neg x) = x)
      (MV₃ : ∀ a : α, add (neg zero) a = neg zero)
      (MV₄ : ∀ x y : α, add (neg (add (neg x) y)) y = add (neg (add (neg y) x)) x)

    example {α : Type} (mv : MV α) : mv.add (mv.zero) (mv.zero) = mv.zero := by
      exact mv.zero_add mv.zero

    set_option checkBinderAnnotations false

    def MV.one {α : Type} [mv : MV α] := mv.neg mv.zero
    def MV.disj {α : Type} [mv : MV α] (x y : α) := mv.add (mv.diff x (mv.neg y)) y
    def MV.conj {α : Type} [mv : MV α] (x y : α) := mv.diff (mv.add x (mv.neg y)) y
    def MV.dist {α : Type} [mv : MV α] (x y : α) := mv.add (mv.diff x (mv.neg y)) (mv.diff y (mv.neg x))
    def MV.mul_zero {α : Type} [mv : MV α] := ∀ x : α, mv.mul 0 x = mv.zero
    def MV.mul_rule {α : Type} [mv : MV α] (n : Float) (x : α) := mv.add x (mv.mul (n - 1) x)

    structure interval01 :=
      (list : List Float)
      (pos : ∀ x : Float, (List.elem x list) → 0 ≤ x)
      (subunit : ∀ x : Float, (List.elem x list) → x ≤ 1)

    #check MV.diff

    structure DMV (α : Type) extends MV α :=
      (r_values : interval01)
      (DMV₁ : ∀ r : Float, ∀ x y : α, List.elem r r_values.list → mul r x = mul r y)
      (DMV₂ : ∀ r q : Float, ∀ x : α, List.elem r r_values.list → List.elem q r_values.list
        → mul (r * (1-q)) x = neg (add (neg (mul r x)) (neg (neg (mul r y)))))
      (DMV₃ : ∀ r q : Float, ∀ x : α, List.elem r r_values.list → List.elem q r_values.list
        → mul r (mul q x) = mul (r * q) x)
      (DMV₄ : ∀ x : α, mul 1 x = x)

  end MVAlgebra

  section LinearAlgebra

    open List

    def Vector (α : Type) (n : Nat) := Fin n → α
    def Matrix (α : Type) (m n : Nat) := Fin m → Vector α n

    def list2vector {α : Type} (l : List α) (n : Nat) (h : n = l.length) : Vector α n :=
      fun i : Fin n =>
      match i with
      | ⟨i, hi⟩ => l.get ⟨i, by {
        apply Nat.lt_of_lt_of_le hi
        exact Nat.le_of_eq (by exact h)
      }⟩

    def list2matrix {α : Type} (ll : List (List α)) (m n : Nat) (h : m = ll.length) : Matrix α m n :=
      fun i => list2vector (ll.get ⟨i.val, by {
        apply Nat.lt_of_lt_of_le i.isLt
        exact Nat.le_of_eq (by exact h)
      }⟩) n (by {
        -- Proof that each sublist has length n needs to be provided or assumed
        sorry
      })



    -- def index {α : Type} (v : Vector α n) (i : Nat) : Option α :=
    --   if h : i < n then
    --     some $ v ⟨i, h⟩
    --   else
    --     none

      -- it is left with sorry so that it is not necessary to write the hypothesis with i < n everytime
      def index {α : Type} (v : Vector α n) (i : Nat) : α := v ⟨i, by sorry ⟩


    -- class DefaultType (α : outParam Type) where
    --   default : α

    -- instance : DefaultType Int where
    --   default := 0

    -- instance : DefaultType Float where
    --   default := 0

    -- instance : DefaultType Nat where
    --   default := 0

    -- #check List

    -- theorem range_n_has_length_n (n : Nat) : n = length (range n) := by
    --   induction n
    --   case zero => rfl
    --   case succ n ih =>
    --     rw [List.range, ih]
    --     sorry

    -- def defaultVector {α : Type} [DefaultType α] (n : Nat) : Vector α n :=
    --   list2vector (map (fun _ => DefaultType.default) (range n)) n (by
    --     simp [*]
    --     exact range_n_has_length_n n
    --   )

    -- instance (α : Type) (n : Nat) [DefaultType α] : DefaultType $ Vector α n where
    --   default := defaultVector n

    -- def fromOption {α : Type} (option : Option α) : α :=
    --   match option with
    --   | some value => value
    --   | none => DefaultType.default

    notation v " [ " i " ] " => index v i

    def vector2list {α : Type} {n : Nat} (v : Vector α n) : List α :=
      map (fun i => v [i]) (range n)

    instance {α : Type} [Repr α] {n : Nat} : Repr (Vector α n) where
      reprPrec v _ :=
        let elems := vector2list v
        "Vector " ++ repr elems

    def matrix2list {α : Type} {n m : Nat} (m : Matrix α n m) : List $ List α :=
      map (fun i => vector2list $ m [i]) (range n)

    instance {α : Type} [Repr α] {n m : Nat} : Repr (Matrix α n m) where
      reprPrec m _ :=
        let elems := matrix2list m
        "Matrix " ++ repr elems

    def elementwiseDiff { α : Type } [HSub α α α] [HAdd α α α] [OfNat α 0]
      (v₁ : Vector α n) (v₂ : Vector α n) : Vector α n := fun i => v₁ [i] - v₂ [i]

    notation v₁ " -V " v₂ => elementwiseDiff v₁ v₂

    def dot_product { α : Type } [HMul α α α] [HAdd α α α] [OfNat α 0]
      (v w : Vector α n) : α :=
      foldr (fun x y => x + y) 0 $
      map (fun (x, y) => x * y)
      (Array.zip
        (map (fun i => v [i]) (range n)).toArray
        (map (fun i => w [i]) (range n)).toArray).toList

    notation v " ⬝ " w => dot_product v w

    def indexes (matrix : Matrix α m n) (i j : Nat) (hi : i < m) (hj : j < n)
      := matrix ⟨ i, by assumption ⟩ ⟨ j, by assumption ⟩

    notation m " [ " i " , " j " ] " => indexes m i j (by simp) (by simp)

    def list_times_vector { α : Type } [HMul α α α] [HAdd α α α] [OfNat α 0] [Inhabited α] { n : Nat }
      (list : List α)
      (vector : Vector α n) : α :=
      foldr (fun x y => x + y) 0 $ map (fun i => list.get! i * vector [i]) (range n)

    def vector_times_list { α : Type } [HMul α α α] [HAdd α α α] [OfNat α 0] [Inhabited α] { n : Nat }
      (vector : Vector α n)
      (list : List α): α := list_times_vector list vector

    notation list " ×LV " vector => list_times_vector list vector
    notation vector " ×VL " list => vector_times_list vector list

    def transpose {α : Type} {m n : Nat} (mat : Matrix α m n) : Matrix α n m :=
      fun i j => mat j i

    notation "T( " matrix " )" => transpose matrix

    def matrix_product {α : Type} [HMul α α α] [HAdd α α α] [OfNat α 0]
      {m n p : Nat}
      (A : Matrix α m n)
      (B : Matrix α n p) : Matrix α m p :=
      fun i => fun j =>
        let row_i := A [i]
        let col_j := (fun k => B k j)
        let dot_prod := row_i ⬝ col_j
        dot_prod

    notation m₁ " ×M " m₂ => matrix_product m₁ m₂

    def mapVector {α β : Type} {n : Nat} (f : α → β) (v : Vector α n) : Vector β n :=
      fun i => f (v i)

    notation f " <$>V " v => mapVector f v

    def mapMatrix {α β : Type} {m n : Nat} (f : α → β)
      (mat : Matrix α m n) : Matrix β m n :=
      fun i j => f (mat i j)

    notation f " <$>M " matrix => mapMatrix f matrix

    def matrix_dot_vector {α : Type} [HMul α α α] [HAdd α α α] [OfNat α 0]
      (matrix : Matrix α m n)
      (vector : Vector α n)
      : Matrix α m 1 := fun i _ => matrix[i] ⬝ vector

    notation matrix " × " vector => matrix_dot_vector matrix vector

    section Example2
      def vector : Vector Float 3 := fun i => match i with
        | ⟨0, _⟩ => 0.4 | ⟨1, _⟩ => 0.5 | ⟨2, _⟩ => 0.6
      #eval vector ⬝ vector

      def vector₂ : Vector Float 3 := fun i => match i with
        | ⟨0, _⟩ => 0.2 | ⟨1, _⟩ => 0.52 | ⟨2, _⟩ => 0.78

      def matrix : Matrix Float 2 3 :=
        fun i => match i with
        | ⟨0, _⟩ => fun j => match j with
          | ⟨0, _⟩ => 0.1 | ⟨1, _⟩ => 0.2  | ⟨2, _⟩ => 0.3
        | ⟨1, _⟩ => fun j => match j with
          | ⟨0, _⟩ => 0.4  | ⟨1, _⟩ => 0.5 | ⟨2, _⟩ => 0.6

      #check matrix × vector
      #eval (matrix × vector) [0, 0]

      #check T(matrix)

      #eval ((fun x => x) <$>M (matrix ×M (T(matrix)))) [1,1]

      #eval (foldr (fun x y => x + y) 0 $ map (fun i => (vector [i] - vector₂ [i]) ^ 2) (range 3)) * 1 / 3

      #check [Vector Nat 2, Vector Nat 3]
      #eval List.get! [1,2,3] 1


      def random_list [HDiv Nat Nat $ IO Nat] (size : Nat) : IO (List Float) :=
        let rec loop (n : Nat) (acc : List Float) : IO (List Float) :=
          if n = 0 then
            return acc
          else do
            let r ← IO.rand 0 100
            loop (n - 1) (List.append [Nat.toFloat (r/100)] acc)
        loop size []

    end Example2

  end LinearAlgebra

  section MultiLayerPerceptron
    open List

    def layer_activation {α : Type} [HAdd α α α] [HMul α α α] [OfNat α 0]
      (input_lines neuronsCurrent neuronsNew : Nat)
      (H : Matrix α input_lines neuronsCurrent)
      (W : Matrix α neuronsNew neuronsCurrent)
      (f : α → Float)
      : Matrix Float input_lines neuronsNew :=
        f <$>M (H ×M T(W))

    def ForwardPropagation
      (H : Matrix Float input_lines input_size)
      (W : Matrix Float output_size input_size)
      (f : Float → Float) : Matrix Float input_lines output_size :=
      layer_activation input_lines input_size output_size H W f

    def BackwardPropagation
      (H : Matrix Float input_lines input_size)
      (W : Matrix Float output_size input_size)
      (f' : Float → Float) : Matrix Float input_size output_size :=
      let delta := (fun z => z * f' z)
        <$>M (layer_activation input_lines input_size output_size H W f')
      let grad_W := (fun x => 1 / input_lines.toFloat * x) <$>M (T(H) ×M delta)
      grad_W

  end MultiLayerPerceptron

  section Example3
      def test_input_layer : Matrix Float 2 1 := fun i => match i with
        | ⟨0, _⟩ => fun j => match j with
          | ⟨0, _⟩ => 0.35
        | ⟨1, _⟩ => fun j => match j with
          | ⟨0, _⟩ => 0.7

      def weights : Matrix Float 2 2 := fun i => match i with
        | ⟨0, _⟩ => fun j => match j with
          | ⟨0, _⟩ => 0.2 | ⟨1, _⟩ => 0.2
        | ⟨1, _⟩ => fun j => match j with
          | ⟨0, _⟩ => 0.3 | ⟨1, _⟩ => 0.3

      #eval (T(test_input_layer) ×M T(weights))
      #eval (ForwardPropagation T(test_input_layer) weights (fun x => min 1 $ max 0 x))
    end Example3

  section ManySortedHybridLogic

    def σ : Nat := 100

    notation s " ++ₛ " t => String.append s t

    inductive sort (σ : Nat)
    | atom : Fin σ → sort σ
    deriving Repr

    def showSort {σ : Nat} (s : sort σ) : String :=
      match s with
      | sort.atom x => "sort " ++ (toString x)

    notation "#s" s => sort.atom (s : Fin 100)

    inductive nominal (σ : Nat)
    | atom : Fin σ → nominal σ
    | nominal : Float → nominal σ
    deriving Repr

    def showNominal {σ : Nat} (n : nominal σ) : String :=
      match n with
      | nominal.atom n => "nominal " ++ (toString n)
      | nominal.nominal r => "γ" ++ toString r

    notation "#n" x => nominal.atom (x : Fin 100)
    notation "#γ" r => ((nominal.nominal r) : nominal 100)

    inductive action (σ : Nat)
    | atom : Fin σ → action σ
    | train : Matrix Float n m → Float → action σ
    | update : Float → Vector (Matrix Float n m) k → Vector Float k → action σ
    | Stop : Vector (Matrix Float n m) k → Vector Float k → action σ
    | seq : action σ → action σ → action σ
    deriving Repr

    def showAction {σ : Nat} (α : action σ) : String :=
      match α with
      | action.atom a => "action " ++ₛ (toString a)
      | action.train W b => "train"
      | action.update η W b => "update " ++ₛ (toString η)
      | action.Stop W b => "Stop"
      | action.seq α β => (showAction α) ++ₛ (" ; " ++ (showAction β))


    notation "#a" a => action.atom (a : Fin 100)
    notation α " ; " β => action.seq α β


    inductive form (σ : Nat) : Type where
    | atom : Fin σ → form σ
    | nomToForm : nominal σ → form σ
    | neg : form σ → form σ
    | oplus : form σ → form σ → form σ
    | sigma : Set (form σ) → form σ
    | hybrid : nominal σ → sort σ → form σ → form σ
    | nom : nominal σ → form σ → form σ
    | diam : nominal σ → form σ → form σ
    | program : action σ → form σ → form σ
    | program_memory : action σ → form σ → form σ → form σ
    | list : List (form σ) → form σ
    | modalImplication : form σ → form σ → form σ
    | negation : form σ → form σ
    | bot : form σ
    | and : form σ → form σ → form σ
    deriving Repr



    def showForm {σ : Nat} (φ : form σ) : String :=
      match φ with
      | form.atom p => "(#" ++ₛ ((toString p) ++ₛ ")")
      | form.nomToForm nom => "(" ++ₛ (showNominal nom ++ₛ ")")
      | form.neg φ => "(¬L" ++ₛ (showForm φ ++ₛ ")")
      | form.oplus φ ψ => "(" ++ₛ ((showForm φ) ++ₛ ("⊕" ++ ((showForm ψ) ++ₛ ")")))
      | form.sigma _ => ""
      | form.hybrid nom sort ψ => "@" ++ₛ ((showNominal nom) ++ₛ ((showSort sort) ++ₛ (showForm ψ)))
      | form.nom nom φ => "(" ++ₛ (showNominal nom ++ₛ ((showForm φ) ++ ")"))
      | form.diam nom ψ => "(◇" ++ₛ (showNominal nom ++ₛ (" " ++ (showForm ψ)))
      | form.program _ _ => ""
      | form.program_memory _ _ _ => ""
      | form.list _ => ""
      | form.modalImplication φ ψ => "(" ++ₛ ((showForm φ) ++ₛ (" ⊃ " ++ₛ ((showForm ψ) ++ₛ ")")))
      | form.negation φ => "(¬" ++ₛ (showForm φ ++ₛ ")")
      | form.and φ ψ => "(" ++ₛ ((showForm φ) ++ₛ (" & " ++ ((showForm ψ) ++ₛ ")")))
      | form.bot => "⊥"

    notation " #p " p => form.atom (p : Fin 100)
    notation " ¬L " p => form.neg p
    notation p " ⊕ " q => form.oplus p q

    notation p " ⊙ " q => ¬L((¬L p) ⊕ (¬L q))
    notation p " →L " q => (¬L p) ⊕ q
    notation p " ⋁ " q => (p ⊙ (¬L q)) ⊕ q
    notation p " ⋀ " q => (p ⊕ (¬L q)) ⊙ q
    notation " ◇ " r " , " p => form.diam r p
    notation " @@ " j " , " s " : " φ => form.hybrid j s φ
    notation " @@ " x " , " φ => form.nom x φ
    notation " [ " α " ] " φ => form.program α φ
    notation " [ " α " ] ⟪ " ν " , " φ " ⟫ " => form.program_memory α ν φ
    notation φ " ⊃ " ψ => form.modalImplication φ ψ
    notation "~" φ => form.negation φ
    notation φ " & " ψ => form.and φ ψ
    notation "⊥" => form.bot

    notation " zL " => (form.nomToForm $ #γ 0)

    def evalNominal (x : nominal σ) : Float :=
      match x with
      | nominal.atom _ => 0
      | nominal.nominal f => f

    def evalForm (φ : form σ) : Float :=
      match φ with
      | form.atom _ => 0
      | form.nomToForm x => evalNominal x
      | form.neg ψ => 1 - evalForm ψ
      | form.oplus ψ χ => min 1 $ (evalForm ψ) + (evalForm χ)
      | form.sigma _ => 0
      | form.hybrid _ _ _ => 0
      | form.nom n _ => evalNominal n
      | form.diam n ψ => (evalNominal n) * (evalForm ψ)
      | form.program _ _ => 0
      | form.program_memory _ _ _ => 0
      | form.list _ => 0
      | form.modalImplication _ _ => 0
      | form.negation _ => 0
      | form.and _ _ => 0
      | form.bot => 0

    def getSome (φ : Option $ form σ) : form σ :=
      match φ with
      | some ψ => ψ
      | none => zL

    set_option trace.PrettyPrinter true

    @[reducible]
    def ctx (σ : Nat) : Type := Set $ form σ

    open action
    open form
    open DMV
    open List

    def vector_product_list [Inhabited (form σ)] [OfNat (Fin σ) 0]
      (n : Nat)
      (w : Vector Float n)
      (lform : List (form σ)) : form σ :=
      foldr (fun φ ψ => oplus φ ψ) (#p 0) $ map (fun i => ◇(#γ w [i]), lform.get! i) (range n)

    def vector2 : Vector Float 2 := fun i => match i with
      | ⟨0,_⟩ => 1 | ⟨1, _⟩ => 2

    def compose_trains {n m k : Nat} (compositions : Nat) (W : Vector (Matrix Float n m) k) (b : Vector Float k) : action σ :=
      match compositions with
      | 0 => train T(W [0]) (b [0])
      | c + 1 => train T(W [c + 1]) (b [c + 1]) ; compose_trains c W b

    def neuron_activation_form { n m : Nat } (b : Float) (W : Matrix Float n m) (φ : form σ) (inputIndex : Nat) : form σ :=
      nomToForm (#γ b) ⊕ foldr (fun φ ψ => φ ⊕ ψ) zL $ map (fun i => ◇(#γ (((matrix2list W).get! inputIndex).get! i)), φ) (range n)

    def layer_activation_form { n m : Nat } (b : Float) (W : Matrix Float n m) (lφ : List $ form σ) : List $ form σ :=
      map (fun (φ, i) => neuron_activation_form b W φ i) $ zip lφ (range (lφ.length))

    def network_training { n m k : Nat } (b : Vector Float k) (W : Vector (Matrix Float n m) k) (lφ : List $ form σ) : form σ :=
      let rec layer_activation_form
      (index : Nat)
      (current_form : form σ) : form σ :=
      match index with
      | 0 => current_form
      | l + 1 =>
        let Wl : Matrix Float n m := W [l]
        let bl : Float := b [l]
        let transformed_form : form σ := neuron_activation_form bl Wl current_form n
        layer_activation_form l (transformed_form)
        let initial_form : form σ := foldr (fun acc φ => φ ⊕ acc) zL lφ
        layer_activation_form k initial_form

    section SymbolicTraining
      def inputs : List $ form σ := [nomToForm $ #γ 0.2, nomToForm $ #γ 0.3]
      def w1 : List $ List Float := [[0.1, 0.2], [0.13, 0.03], [0.11, 0.1]]
      def w2 : List $ List Float := [[0.3, 0.67, 0.15]]
      def b : List $ Float := [0.08, 0.18]

      def w1_matrix : Matrix Float 3 2 := list2matrix w1 3 2 (by rfl)
      def w2_matrix : Matrix Float 1 3 := list2matrix w2 1 3 (by rfl)
      def b_vector : Vector Float 2 := list2vector b 2 (by rfl)

      def layer_1 : List $ form σ := layer_activation_form (b.get! 0) w1_matrix inputs
      def layer_2 : List $ form σ := layer_activation_form (b.get! 1) w2_matrix layer_1

      def predicted : form σ := getSome (layer_2.get? 0)

      #eval predicted
      #eval showForm predicted
      #eval evalForm predicted
    end SymbolicTraining


    def dL (x y : form σ) : form σ := (x ⊙ (¬L y)) ⊕ (y ⊙ (¬L x))


    inductive Proof [Inhabited (form σ)] [Inhabited (nominal σ)] [OfNat (Fin σ) 0] : ctx σ → form σ → Prop
    | ax { Γ } { p : form σ } (h : p ∈₁ Γ) : Proof Γ p
    | NOM₁₁ { Γ } { r : Float } { DMV : DMV Float} (h : Proof Γ $ nomToForm (#γ (DMV.neg r)))
        : Proof Γ $ ¬L (nomToForm (#γ r))
    | NOM₁₂ { Γ } { r : Float } { DMV : DMV Float} (h : Proof Γ $ ¬L (nomToForm (#γ r)))
        : Proof Γ $ nomToForm (#γ (DMV.neg r))
    | NOM₂₁ { Γ } { r q : Float } { DMV : DMV Float } (h : Proof Γ $ nomToForm (#γ (DMV.add r q)))
        : Proof Γ $ (nomToForm (#γ r)) ⊕ (nomToForm (#γ q))
    | NOM₂₂ { Γ } { r q : Float } { DMV : DMV Float } (h : Proof Γ $ (nomToForm (#γ r)) ⊕ (nomToForm (#γ q)))
        : Proof Γ $ nomToForm (#γ (DMV.add r q))
    | NOM₃₁ { Γ } { r q : Float } { DMV : DMV Float } (h : Proof Γ $ nomToForm (#γ (DMV.mul r q)))
        : Proof Γ $ ◇(#γ r), (nomToForm $ #γ q)
    | NOM₃₂ { Γ } { r q : Float } { DMV : DMV Float } (h : Proof Γ $ ◇(#γ r), (nomToForm $ #γ q))
        : Proof Γ $ nomToForm (#γ (DMV.mul r q))
    | M₁₁ { Γ } { φ ψ χ : form σ } (h : Proof Γ $ (φ ⊕ (ψ ⊕ χ)))
        : Proof Γ $ (φ ⊕ (ψ ⊕ χ))
    | M₁₂ { Γ } { φ ψ χ : form σ } (h : Proof Γ $ (φ ⊕ (ψ ⊕ χ)))
        : Proof Γ $ (φ ⊕ (ψ ⊕ χ))
    | M₂₁ { Γ } { φ ψ : form σ } (h : Proof Γ $ (φ ⊕ ψ))
        : Proof Γ $ (ψ ⊕ φ)
    | M₂₂ { Γ } { φ ψ : form σ } (h : Proof Γ $ (ψ ⊕ φ))
        : Proof Γ $ (φ ⊕ ψ)
    | M₃ { Γ } { φ : form σ } : Proof Γ $ @@(#γ 0),φ
    | M₄₁ { Γ } { φ : form σ } (h : Proof Γ $ (¬L (¬L φ)))
        : Proof Γ $ φ
    | M₄₂ { Γ } { φ : form σ } (h : Proof Γ $ φ )
        : Proof Γ $ (¬L (¬L φ))
    | M₅₁ { Γ } { φ : form σ } (h : Proof Γ $ ((¬L zL) ⊕ φ))
        : Proof Γ $ (¬L zL)
    | M₅₂ { Γ } { φ : form σ } (h : Proof Γ $ (¬L zL))
        : Proof Γ $ ((¬L zL) ⊕ φ)
    | M₆₁ { Γ } { φ ψ : form σ } (h : Proof Γ $ (¬L((¬L φ) ⊕ ψ)) ⊕ ψ)
        : Proof Γ $ (¬L((¬L ψ) ⊕ φ)) ⊕ φ
    | M₆₂ { Γ } { φ ψ : form σ } (h : Proof Γ $ (¬L((¬L ψ) ⊕ φ)) ⊕ φ )
        : Proof Γ $ (¬L((¬L φ) ⊕ ψ)) ⊕ ψ
    | R₁₁ { Γ } { r : Float } { φ ψ : form σ } (h : Proof Γ $ ◇(#γ r), (φ ⊙ (¬L ψ)))
        : Proof Γ $ ((◇(#γ r),φ) ⊙ (¬L (◇(#γ r),ψ)))
    | R₂₁ { Γ } { r : Float } { φ ψ : form σ } (h : Proof Γ $ ((◇(#γ r),φ) ⊙ (¬L (◇(#γ r),ψ))))
        : Proof Γ $ ◇(#γ r), (φ ⊙ (¬L ψ))
    | R₃₁ { Γ } { r q : Float } { φ : form σ } (h : Proof Γ $ (◇ (#γ r), (◇ (#γ q), φ) ))
        : Proof Γ $ ◇ (#γ (r * q)), φ
    | R₃₂ { Γ } { r q : Float } { φ : form σ } (h : Proof Γ $ ◇ (#γ (r * q)), φ)
        : Proof Γ $  (◇ (#γ r), (◇ (#γ q), φ) )
    | R₄₁ { Γ } { φ : form σ } (h : Proof Γ $ (◇(#γ 1), φ))
        : Proof Γ $ φ
    | R₄₂  { Γ } { φ : form σ } (h : Proof Γ $ φ)
        : Proof Γ $ (◇(#γ 1), φ)
    | MP { Γ } { φ ψ : form σ } (hφ : Proof Γ φ) (hφψ : Proof Γ $ φ ⊃ ψ) : Proof Γ $ ψ
    | MT { Γ } {φ ψ : form σ} (hφψ : Proof Γ $ φ ⊃ ψ) (hnψ : Proof Γ $ (~ψ)) : Proof Γ $ (~φ)
    | Deduction { Γ } {φ ψ : form σ} (h : Proof Γ $ φ ⊃ ψ) : Proof Γ φ → Proof Γ ψ
    | introAnd { Γ } {φ ψ : form σ} (h₀ : Proof Γ φ) (h₁ : Proof Γ ψ) : Proof Γ $ (φ & ψ)
    | introNegation { Γ } {φ : form σ} (h : Proof Γ $ (~φ) ⊃ ⊥) : Proof Γ φ
    | introAbsurd { Γ } {φ : form σ} (hp : Proof Γ φ) (hnp : Proof Γ $ ~φ ) : Proof Γ ⊥
    | byAbsurd { Γ } {φ : form σ} (h_absurd : Proof Γ ⊥) : Proof Γ φ
    | dne { Γ } {φ : form σ} (h : Proof Γ $ ~(~φ)) : Proof Γ φ
    | dni { Γ } {φ : form σ} (h : Proof Γ φ) : Proof Γ $ ~(~φ)
    | N₀₁ { Γ } { ν : form σ } { α β : action σ } (h : Proof Γ $ [α ; β]ν) : Proof Γ $ [β][α]ν
    | N₀₂ { Γ } { ν : form σ } { α β : action σ } (h : Proof Γ $ [β][α]ν) : Proof Γ $ [α ; β]ν
    | N₁ { Γ } { n : Nat } { W : Matrix Float n m } { b : Float } {DMV : DMV Float}
      { lφ : List $ form σ }
      (h : Proof Γ $ [train W b] (list lφ))
        : Proof Γ $ list $ layer_activation_form b W lφ
    | N₂ { Γ } { n : Nat } { lφ : List (form σ) } { X : List (nominal σ)} { ln : sort σ }
      (h : Proof Γ $ foldr (fun φ ψ => φ ⋀ ψ) (lφ.get! 0) $ map (fun i => @@(X.get! i),ln:lφ.get! i) (range n) )
      : Proof Γ $ list lφ →L list (map (fun i => nomToForm $ X.get! i) (range n))
    | N₃ { Γ } {n m k : Nat} {lφ : List $ form σ} {W : Vector (Matrix Float n m) k} {b : Vector Float k} {ν : form σ} {ln : sort σ } {y ε η : Float}
      (h₀ : Proof Γ $ ([compose_trains k W b]ν) →L (list lφ))
      (h₁ : Proof Γ $ ~ @@(#n 1),ln:((dL (nomToForm (#γ y)) (foldr (fun φ ψ => φ ⋁ ψ) zL lφ)) →L (nomToForm (#γ ε))))
      : Proof Γ $ [update η W b]ν
    | N₄ { Γ } {n m k : Nat} {lφ : List $ form σ} {W : Vector (Matrix Float n m) k} {b : Vector Float k} {ν : form σ} {ln : sort σ } {y ε η : Float}
      (h₀ : Proof Γ $ ([compose_trains k W b]ν) →L (list lφ))
      (h₁ : Proof Γ $ @@(#n 1),ln:((dL (nomToForm (#γ y)) (foldr (fun φ ψ => φ ⋁ ψ) zL lφ)) →L (nomToForm (#γ ε))))
      : Proof Γ $ [Stop W b]((#p 0) ⋁ ¬L(#p 0))
    | N₅ { Γ } {n m k : Nat} {lφ : List $ form σ} {W : Vector (Matrix Float n m) k} {b : Vector Float k} {ν : form σ} {ln : sort σ } {y ε η : Float}
      (h : Proof Γ $ [update η W b]ν)
      : Proof Γ $ [compose_trains k W b]ν
    | I { Γ } {n k : Nat} {W : Vector (Matrix Float n m) k} {b : Vector Float k} (lh : Vector Float n)
      : Proof Γ $ [compose_trains k W b](list $ map (fun h => nomToForm (#γ h)) (vector2list lh))
    | I_mem { Γ } {n k : Nat} {W : Vector (Matrix Float n m) k} {b : Vector Float k} (lh : Vector Float n)
      : Proof Γ $ [compose_trains k W b] ⟪zL, (list $ map (fun h => nomToForm (#γ h)) (vector2list lh))⟫
    | N₃_mem { Γ } {n m k : Nat} {lφ : List $ form σ} {W : Vector (Matrix Float n m) k} {b : Vector Float k} {ν : form σ} {ln : sort σ } {y ε η : Float}
      {m : form σ } {E : Float}
      (h₀ : Proof Γ $ ([compose_trains k W b] ⟪m, ν⟫) ⊃ (list lφ))
      (h₁ : Proof Γ $ (@@(#n 1),ln:dL m (nomToForm (#γ ((E - 1)/E)))))
      (h₂ : Proof Γ $ ~ @@(#n 1),ln:((dL (nomToForm (#γ y)) (foldr (fun φ ψ => φ ⋁ ψ) (zL) lφ)) →L (nomToForm (#γ ε))))
      : Proof Γ $ [update η W b] ⟪m ⊕ nomToForm (#γ 1/E), ν⟫
    | N₃'_mem { Γ } {n m k : Nat} {lφ : List $ form σ} {W : Vector (Matrix Float n m) k} {b : Vector Float k} {ν : form σ} {ln : sort σ } {y ε η : Float}
      {m : form σ } {E : Float}
      (h₀ : Proof Γ $ ([compose_trains k W b] ⟪m, ν⟫) →L (list lφ))
      (h₁ : Proof Γ $ ~ @@(#n 1),ln:((dL (nomToForm (#γ y)) (foldr (fun φ ψ => φ ⋁ ψ) zL lφ)) →L (nomToForm (#γ ε))))
      : Proof Γ $ [Stop W b] ⟪nomToForm $ #γ 1, (#p 0) ⋀ ¬L(#p 0)⟫
    | N₄_mem { Γ } {n m k : Nat} {lφ : List $ form σ} {W : Vector (Matrix Float n m) k} {b : Vector Float k} {ν : form σ} {ln : sort σ } {y ε η : Float}
      {m : form σ}
      (h₀ : Proof Γ $ ([compose_trains k W b] ⟪m, ν⟫) →L (list lφ))
      (h₁ : Proof Γ $ @@(#n 1),ln:((dL (nomToForm (#γ y)) (foldr (fun φ ψ => φ ⋁ ψ) zL lφ)) →L (nomToForm (#γ ε))))
      : Proof Γ $ [Stop W b] ⟪m, ((#p 0) ⋁ ¬L(#p 0))⟫
    | N₅_mem { Γ } {n m k : Nat} {lφ : List $ form σ} {W : Vector (Matrix Float n m) k} {b : Vector Float k} {ν : form σ} {ln : sort σ } {y ε η E : Float} {m : form σ}
      (h : Proof Γ $ [update η W b] ⟪m, ν⟫)
      : Proof Γ $ [compose_trains k W b] ⟪m, ν⟫

    notation Γ " ⊢ " φ => Proof Γ φ

    axiom toPropImpl [Inhabited $ form σ] [Inhabited $ nominal σ] [OfNat (Fin σ) 0]
      {Γ : ctx σ} {φ ψ : form σ} : ((Γ ⊢ φ) → (Γ ⊢ ψ)) ↔ (Γ ⊢ (φ ⊃ ψ))
    axiom toPropNeg [Inhabited $ form σ] [Inhabited $ nominal σ] [OfNat (Fin σ) 0]
      {Γ : ctx σ} {φ : form σ} : (Γ ⊢ (~φ)) ↔ (¬(Γ ⊢ φ))
    axiom toPropDecide_N₃N₄N₄' [Inhabited $ form σ] [Inhabited $ nominal σ] [OfNat (Fin σ) 0]
      {Γ : ctx σ} {n m k : Nat} {lφ : List $ form σ} {W : Vector (Matrix Float n m) k} {b : Vector Float k} {ν : form σ} {ln : sort σ } {y ε η : Float}
      {m : form σ } {E : Float} :
      (¬(Γ ⊢ (@@(#n 1),ln:dL m (nomToForm (#γ ((E - 1)/E)))))) → (¬(Γ ⊢ [update η W b] ⟪m ⊕ nomToForm (#γ 1/E), ν⟫))

    theorem φ_provable_by_φ {φ : form σ} [Inhabited $ form σ] [Inhabited $ nominal σ] [OfNat (Fin σ) 0] : (Set.cons φ (Set.nil)) ⊢ φ := by
      have h : φ ∈₁ (Set.cons φ (Set.nil)) := by
        have hself := Set.mem_cons_self φ (Set.nil)
        exact hself
      exact Proof.ax h

    theorem modus_tollens {p q : Prop} : (p → q) → (¬q) → (¬p) := by
      intros hpq hnq
      intro hp
      have hq := hpq hp
      contradiction

    theorem inductive_step_termination {n m k : Nat} {y η ε E : Float} {Γ : ctx σ}
      {W : Vector (Matrix Float n m) k}
      {b : Vector Float k}
      {lφ : List $ form σ}
      {ln : sort σ}
      {mem ν : form σ}
      [inst₁ : Inhabited $ form σ] [inst₂ : Inhabited $ nominal σ] [inst₃: OfNat (Fin σ) 0]
      : (Γ ⊢ ([compose_trains k W b] ⟪mem, ν⟫) ⊃ list lφ)
      → (Γ ⊢ ([update η W b] ⟪mem ⊕ nomToForm (#γ (1/E)), ν⟫))
      → (Γ ⊢ (~ @@(#n 1),ln:((dL (nomToForm (#γ y)) (foldr (fun φ ψ => φ ⋁ ψ) zL lφ)) →L (nomToForm (#γ ε)))))
      → (Γ ⊢ ((@@(#n 1),ln:dL mem (nomToForm (#γ ((E - 1)/E)))) & ([compose_trains k W b] ⟪mem ⊕ nomToForm (#γ (1/E)), ν⟫))) := by
      intros h₁ h₂ h₃
      have n₃ := @Proof.N₃_mem inst₁ inst₂ inst₃ Γ n m k lφ W b ν ln y ε η mem E
      have n₅ := @Proof.N₅_mem inst₁ inst₂ inst₃ Γ n m k lφ W b ν ln y ε η E (mem ⊕ nomToForm (#γ (1/E)))
      have h_false : (Γ ⊢ (~(@@(#n 1),ln:dL mem (nomToForm (#γ ((E - 1)/E)))))) → (Γ ⊢ ⊥) := by
        intro h_local
        rw [@toPropNeg inst₁ inst₂ inst₃ Γ (@@(#n 1),ln:dL mem (nomToForm (#γ ((E - 1)/E))))] at h_local
        have h_continuation := @toPropDecide_N₃N₄N₄' inst₁ inst₂ inst₃ Γ n m k lφ W b ν ln y ε η  mem E h_local
        contradiction
      rw [@toPropImpl inst₁ inst₂ inst₃ Γ (~(@@(#n 1),ln:dL mem (nomToForm (#γ ((E - 1)/E))))) ⊥] at h_false
      have h := Proof.introNegation h_false
      have h₄ := n₅ h₂
      exact Proof.introAnd h h₄

  end ManySortedHybridLogic


section Example4
  open form
  open nominal

  def w_list := [[0.01], [0.3]]
  def w_matrix : Matrix Float 2 1 := list2matrix w_list 2 1 (by rfl)
  def bias : Float := 0.12
  def lφ : List $ form σ := [nomToForm (#γ 2.3), zL]


  def pred_y : form σ := getSome ((layer_activation_form bias w_matrix lφ).get? 0)

  #eval pred_y
  #eval evalForm pred_y
  #eval evalForm $ (dL pred_y (nomToForm $ #γ 0.01)) →L (nomToForm $ #γ 0.01)


end Example4

end Lukasiewicz
