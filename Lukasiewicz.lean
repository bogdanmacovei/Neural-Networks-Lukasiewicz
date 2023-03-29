section Lukasiewicz 

  section Set 
    inductive Set (α : Type) where 
    | nil : Set α 
    | cons : α → Set α → Set α 

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

    notation "[]" => Set.nil 
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
    
    def index (v : Vector α n) (i : Nat) --(h : i < n) 
      := v ⟨ i, by sorry ⟩ 

    notation v " [ " i " ] " => index v i 

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

    end Example2 

  end LinearAlgebra 

  section MultiLayerPerceptron
    open List 

    def layer_activation {α : Type} [HAdd α α α] [HMul α α α] [OfNat α 0]
      (input_lines neuronsCurrent neuronsNew : Nat)
      (Q : Matrix α input_lines neuronsCurrent)
      (W : Matrix α neuronsNew neuronsCurrent) 
      (f : α → Float)
      : Matrix Float input_lines neuronsNew := 
        f <$>M (Q ×M T(W)) 

    def RMSE (input_lines : Nat)
      (test_values : Vector Float input_lines)
      (predicted_values : Vector Float input_lines)
      : Float := 
        (1 / input_lines.toFloat) 
        * (foldr (fun x y => x + y) 0 
          $ map (fun i => (test_values [i] - predicted_values [i]) ^ 2) (range input_lines)) 

    def ForwardPropagation 
      (Q : Matrix Float input_lines input_size) 
      (W : Matrix Float output_size input_size) 
      (f : Float → Float) : Matrix Float input_lines output_size :=
      layer_activation input_lines input_size output_size Q W f

    def BackwardPropagation 
      (Q : Matrix Float input_lines input_size) 
      (W : Matrix Float output_size input_size) 
      (f' : Float → Float) : Matrix Float input_size output_size :=
      let delta := (fun z => z * f' z) 
        <$>M (layer_activation input_lines input_size output_size Q W f')
      let grad_W := (fun x => 1 / input_lines.toFloat * x) <$>M (T(Q) ×M delta)
      grad_W

  end MultiLayerPerceptron

  section ManySortedHybridLogic 

    inductive sort (σ : Nat)
    | atom : Fin σ → sort σ 

    notation "#s" s => sort.atom s 

    inductive nominal (σ : Nat)
    | atom : Fin σ → nominal σ 
    | nominal : Float → nominal σ 

    notation "#n" x => nominal.atom x 
    notation "#γ" r => nominal.nominal r 

    inductive action (σ : Nat)
    | atom : Fin σ → action σ 
    | train : Vector Float n → Float → action σ
    | update : Float → List (Vector Float n) → action σ  
    | stop : List (Vector Float n) → action σ 
    | seq : action σ → action σ → action σ 

    notation "#a" a => action.atom a 
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
    | list : List (form σ) → form σ 

    notation " # " p => form.atom p
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

    notation " zL " => (form.nomToForm $ #γ 0)

    #check [(#a 1) ; (#a 2)]@@(#n 1),(#s 1):(¬L(#1) →L (#2))

    @[reducible]
    def ctx (σ : Nat) : Type := Set $ form σ 

    open action 
    open form 
    open DMV 
    open List 

    def vector_product_list { σ : Nat } [Inhabited (form σ)] [OfNat (Fin σ) 0]
      (n : Nat)
      (w : Vector Float n) 
      (lform : List (form σ)) : form σ := 
      foldr (fun φ ψ => oplus φ ψ) (atom 0) $ map (fun i => ◇(#γ w [i]), lform.get! i) (range n)

    inductive Proof { σ : Nat } [Inhabited (form σ)] [Inhabited (nominal σ)] [OfNat (Fin σ) 0] : ctx σ → form σ → Prop 
    | ax { Γ } { p : form σ } (h : p ∈₁ Γ) : Proof Γ p 
    | Ka { Γ } { φ ψ : form σ } { j : nominal σ } { s : sort σ } (h : Proof Γ $ @@j,s:(φ →L ψ))
        : Proof Γ $ @@j,s:φ →L @@j,s:ψ
    | SelfDual₁ { Γ } { φ : form σ } { j : nominal σ } { s : sort σ } (h : Proof Γ $ @@j,s:φ)
        : Proof Γ $ ¬L@@j,s:(¬Lφ)
    | SelfDual₂ { Γ } { φ : form σ } { j : nominal σ } { s : sort σ } (h : Proof Γ $ ¬L@@j,s:(¬Lφ))
        : Proof Γ $ @@j,s:φ
    | Agree₁ { Γ } { φ : form σ } { k j : nominal σ } { t t' : sort σ } (h : Proof Γ $ @@k,t:(@@j,t':φ))
        : Proof Γ $ @@j,t:φ 
    | Agree₂ { Γ } { φ : form σ } { k j : nominal σ } { t t' : sort σ } (h : Proof Γ $ @@j,t:φ)
        : Proof Γ $ @@k,t:(@@j,t':φ)
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
    | MG₁₁ { Γ } { φ ψ χ : form σ } { x : nominal σ } (h : Proof Γ $ @@x,(φ ⊕ (ψ ⊕ χ)))
        : Proof Γ $ @@x,(φ ⊕ (ψ ⊕ χ))
    | MG₁₂ { Γ } { φ ψ χ : form σ } { x : nominal σ } (h : Proof Γ $ @@x,(φ ⊕ (ψ ⊕ χ)))
        : Proof Γ $ @@x,(φ ⊕ (ψ ⊕ χ))
    | MG₂₁ { Γ } { φ ψ : form σ } { x : nominal σ } (h : Proof Γ $ @@x,(φ ⊕ ψ))
        : Proof Γ $ @@x,(ψ ⊕ φ)
    | MG₂₂ { Γ } { φ ψ : form σ } { x : nominal σ } (h : Proof Γ $ @@x,(ψ ⊕ φ))
        : Proof Γ $ @@x,(φ ⊕ ψ)
    | MG₃ { Γ } { φ : form σ } : Proof Γ $ @@(#γ 0),φ
    | MV₁₁ { Γ } { φ : form σ } { x : nominal σ } (h : Proof Γ $ @@x,(¬L (¬L φ))) 
        : Proof Γ $ @@x,φ 
    | MV₁₂ { Γ } { φ : form σ } { x : nominal σ } (h : Proof Γ $ @@x,φ )
        : Proof Γ $ @@x,(¬L (¬L φ))
    | MV₂₁ { Γ } { φ : form σ } { x : nominal σ } (h : Proof Γ $ @@x,((¬L zL) ⊕ φ))
        : Proof Γ $ @@x, (¬L zL)
    | MV₂₂ { Γ } { φ : form σ } { x : nominal σ } (h : Proof Γ $ @@x, (¬L zL))
        : Proof Γ $ @@x,((¬L zL) ⊕ φ)
    | MV₃₁ { Γ } { φ ψ : form σ } { x : nominal σ } (h : Proof Γ $ @@x, (¬L((¬L φ) ⊕ ψ)) ⊕ ψ) 
        : Proof Γ $ @@x, (¬L((¬L ψ) ⊕ φ)) ⊕ φ 
    | MV₃₂ { Γ } { φ ψ : form σ } { x : nominal σ } (h : Proof Γ $ @@x, (¬L((¬L ψ) ⊕ φ)) ⊕ φ ) 
        : Proof Γ $ @@x, (¬L((¬L φ) ⊕ ψ)) ⊕ ψ
    | R₁₁ { Γ } { r : Float } { φ ψ : form σ } { x : nominal σ } (h : Proof Γ $ @@x,◇(#γ r), (φ ⊙ (¬L ψ)))
        : Proof Γ $ @@x,((◇(#γ r),φ) ⊙ (¬L (◇(#γ r),ψ)))
    | R₂₁ { Γ } { r : Float } { φ ψ : form σ } { x : nominal σ } (h : Proof Γ $ @@x,((◇(#γ r),φ) ⊙ (¬L (◇(#γ r),ψ))))
        : Proof Γ $  @@x,◇(#γ r), (φ ⊙ (¬L ψ))
    | N₀₁ { Γ } { ν : form σ } { α β : action σ } (h : Proof Γ $ [α ; β]ν) : Proof Γ $ [α][β]ν 
    | N₀₂ { Γ } { ν : form σ } { α β : action σ } (h : Proof Γ $ [α][β]ν) : Proof Γ $ [α ; β]ν
    | N₁ { Γ } { n : Nat } { w : Vector Float n } { b : Float } {DMV : DMV Float} 
      { lφ : List $ form σ } 
      (h : Proof Γ $ [train w b] (list lφ)) 
        : Proof Γ $ list (map (fun _ => nomToForm (#γ b) ⊕ (vector_product_list n w lφ)) (range n))
    | N₂ { Γ } { n : Nat } { lφ : List (form σ) } { X : List (nominal σ)} { ln : sort σ }
      (h : Proof Γ $ foldr (fun φ ψ => φ ⋀ ψ) (lφ.get! 0) $ map (fun i => @@(X.get! i),ln:lφ.get! i) (range n) )
      : Proof Γ $ list lφ →L list (map (fun i => nomToForm $ X.get! i) (range n))

    notation Γ " ⊢ " p => Proof Γ p 

  end ManySortedHybridLogic 
    def w1 : Matrix Float 5 3 := 
      fun i => match i with 
        | ⟨0, _⟩ => fun j => match j with
          | ⟨0, _⟩ => 0.9811 | ⟨1, _⟩ => 0.3531 | ⟨2, _⟩ => 0.1121
        | ⟨1, _⟩ => fun j => match j with
          | ⟨0, _⟩ => 0.4517 | ⟨1, _⟩ => 0.6646 | ⟨2, _⟩ => 0.2132
        | ⟨2, _⟩ => fun j => match j with
          | ⟨0, _⟩ => 0.5921 | ⟨1, _⟩ => 0.3788 | ⟨2, _⟩ => 0.1211
        | ⟨3, _⟩ => fun j => match j with
          | ⟨0, _⟩ => 0.1891 | ⟨1, _⟩ => 0.4145 | ⟨2, _⟩ => 0.1213
        | ⟨4, _⟩ => fun j => match j with
          | ⟨0, _⟩ => 0.6381 | ⟨1, _⟩ => 0.1213 | ⟨2, _⟩ => 0.3121

    def w2 : Matrix Float 2 5 := 
      fun i => match i with 
        | ⟨0, _⟩ => fun j => match j with
          | ⟨0, _⟩ => 0.1424 | ⟨1, _⟩ => 0.2341 | ⟨2, _⟩ => 0.1131 | ⟨3, _⟩ => 0.3122 | ⟨4, _⟩ => 0.5412
        | ⟨1, _⟩ => fun j => match j with
          | ⟨0, _⟩ => 0.1212 | ⟨1, _⟩ => 0.5671 | ⟨2, _⟩ => 0.8181 | ⟨3, _⟩ => 0.7671 | ⟨4, _⟩ => 0.3119

    def w3 : Matrix Float 1 2 :=
      fun i => match i with 
        | ⟨0, _⟩ => fun j => match j with
            | ⟨0, _⟩ => 0.7172
            | ⟨1, _⟩ => 0.1231

    def Q : Matrix Float 4 3 := 
      fun i => match i with 
        | ⟨0, _⟩ => fun j => match j with
          | ⟨0, _⟩ => 0 | ⟨1, _⟩ => 0 | ⟨2, _⟩ => 1
        | ⟨1, _⟩ => fun j => match j with
          | ⟨0, _⟩ => 1 | ⟨1, _⟩ => 0 | ⟨2, _⟩ => 1
        | ⟨2, _⟩ => fun j => match j with
          | ⟨0, _⟩ => 0 | ⟨1, _⟩ => 1 | ⟨2, _⟩ => 0
        | ⟨3, _⟩ => fun j => match j with
          | ⟨0, _⟩ => 1 | ⟨1, _⟩ => 1 | ⟨2, _⟩ => 1

    def ReLU₁ (x : Float) : Float := min 1 $ max 0 x
    def ReLU₁' (x : Float) : Float := 
      if x < 0 
        then 0 
      else if x < 1 
          then 1 
          else 0

    #check ((fun x => min 1 $ max 0 x) <$>M Q ×M T(w1))
    #check ((fun x => min 1 $ max 0 x) <$>M ((fun x => min 1 $ max 0 x) <$>M Q ×M T(w1)) ×M T(w2)) 
    #check 
      ((fun x => ReLU₁ x) <$>M 
        ((fun x => ReLU₁ x) <$>M 
          ((fun x => ReLU₁ x) <$>M 
            Q 
          ×M T(w1)) 
        ×M T(w2)) 
      ×M T(w3)) 

    #eval (BackwardPropagation ((fun x => ReLU₁ x) <$>M 
          ((fun x => ReLU₁ x) <$>M 
            Q 
          ×M T(w1)) 
        ×M T(w2)) w3 ReLU₁') [1,0] 

  section MLPExample

  end MLPExample 
end Lukasiewicz