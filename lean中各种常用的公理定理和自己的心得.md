abs_of_nonneg.{u_1} {α : Type u_1} [Lattice α] [AddGroup α] {a : α}
  [CovariantClass α α (fun x x_1 => x + x_1) fun x x_1 => x ≤ x_1]
  (h : 0 ≤ a) : |a| = a

abs_of_neg.{u_1} {α : Type u_1} [Lattice α] [AddGroup α] {a : α}
  [CovariantClass α α (fun x x_1 => x + x_1) fun x x_1 => x ≤ x_1]
  (h : a < 0) : |a| = -a、

le_or_gt.{u} {α : Type u} [LinearOrder α] (a b : α) : a ≤ b ∨ a > b

constructor用于把证明A↔B变成证明A→B和B→A

constructor还用于把证明A∧B变成证明A和B。从而对于证明A∧B∧C之类的，会变成证明A和B∧C，继续
  用constructor分解即可。

rcases h1 with h2 | h3。h1是AVB,h2是A,h3是B。这之后h1消失，且h2和h3并不同时存在，
  所以其实可以这样起名：rcases h1 with h1 | h1。
  rcases h1 with h2|h3|h4。h1是AVBVC,h2是A,h3是B,h4是C。这之后h1消失，且h2、h3和h4
  并不同时存在，所以其实可以这样起名：rcases h1 with h1 | h1 | h1。有更多'V'的h1以此
  类推。

rcases h1 with ⟨h2, h3⟩。h1是A∧B,h2是A,h3是B。这之后h1消失，h2和h3同时存在，所以
  其实可以这样起名：rcases h1 with h1 | h2。

lt_trichotomy.{u} {α : Type u} [LinearOrder α] (a b : α) : a < b ∨ a = b ∨ b < a

contradiction。如果假设们之间“非常地矛盾”，则关闭目标。

sq_nonneg.{u} {α : Type u} [Semiring α] [LinearOrder α] [IsRightCancelAdd α]
  [ZeroLEOneClass α] [ExistsAddOfLE α][PosMulMono α] [CovariantClass α α
  (fun x x_1 => x + x_1) fun x x_1 => x < x_1] (a : α) : 0 ≤ a ^ 2

NoZeroDivisors.eq_zero_or_eq_zero_of_mul_eq_zero.{u_4} {M₀ : Type u_4} [Mul M₀]
  [Zero M₀] [self : NoZeroDivisors M₀] {a b : M₀} : a * b = 0 → a = 0 ∨ b = 0

eq_neg_iff_add_eq_zero.{u_3} {G : Type u_3} [AddGroup G] {a b : G} :
  a = -b ↔ a + b = 0

eq_of_sub_eq_zero.{u_1} {α : Type u_1} [SubtractionMonoid α] {a b : α}
  (h : a - b = 0) : a = b

assumption。在当前的上下文中寻找与目标（goal）完全匹配的假设，并使用它来解决目标。
  是一个特化的工具，专门用于直接解决目标与已有假设完全匹配的情况

mul_lt_mul_right.{u_1} {α : Type u_1} {a b c : α} [Mul α] [Zero α] [Preorder α]
  [MulPosStrictMono α] [MulPosReflectLT α] (a0 : 0 < a) : b * a < c * a ↔ b < c

one_mul.{u} {M : Type u} [MulOneClass M] (a : M) : 1 * a = a

abs_zero.{u_1} {α : Type u_1} [Lattice α] [AddGroup α]
  [CovariantClass α α (fun x x_1 => x + x_1) fun x x_1 => x ≤ x_1] : |0| = 0

add_lt_add.{u_1} {α : Type u_1} [Add α] [Preorder α] [CovariantClass α α (fun x x_1
  => x + x_1) fun x x_1 => x < x_1][CovariantClass α α (Function.swap fun x x_1 => x
  + x_1) fun x x_1 => x < x_1] {a b c d : α} (h₁ : a < b)(h₂ : c < d) : a + c < b + d

le_of_max_le_left.{u} {α : Type u} [LinearOrder α] {a b c : α} (h : max a b ≤ c) : a ≤ c

le_of_max_le_right.{u} {α : Type u} [LinearOrder α] {a b c : α} (h : max a b ≤ c) : b ≤ c

abs_pos.{u_1} {α : Type u_1} [AddGroup α] [LinearOrder α]
  [CovariantClass α α (fun x x_1 => x + x_1) fun x x_1 => x ≤ x_1] {a : α} : 0 < |a| ↔ a ≠ 0

div_pos.{u_1} {α : Type u_1} [Semifield α] [LinearOrder α] [PosMulReflectLT α]
  [ZeroLEOneClass α] {a b : α} [PosMulStrictMono α] (ha : 0 < a) (hb : 0 < b) : 0 < a / b

mul_lt_mul_of_pos_left.{u_1} {α : Type u_1} {a b c : α} [Mul α] [Zero α] [Preorder α]
  [PosMulStrictMono α] (bc : b < c) (a0 : 0 < a) : a * b < a * c

mul_div_cancel₀.{u_3} {G₀ : Type u_3} [CommGroupWithZero G₀] {b : G₀} (a : G₀) (hb : b ≠ 0)
  : b * (a / b) = a

ne_of_lt.{u} {α : Type u} [Preorder α] {a b : α} (h : a < b) : a ≠ b

abs_add.{u_1} {α : Type u_1} [LinearOrderedAddCommGroup α] (a b : α) : |a + b| ≤ |a| + |b|

lt_of_le_of_lt.{u} {α : Type u} [Preorder α] {a b c : α} (hab : a ≤ b) (hbc : b < c) : a < c

le_refl.{u} {α : Type u} [Preorder α] (a : α) : a ≤ a

mul_lt_mul''.{u_1} {α : Type u_1} {a b c d : α} [MulZeroClass α] [Preorder α]
  [PosMulStrictMono α] [MulPosMono α](h₁ : a < b) (h₂ : c < d) (a0 : 0 ≤ a) (c0 : 0 ≤ c)
  : a * c < b * d

abs_mul.{u_1} {α : Type u_1} [LinearOrderedRing α] (a b : α) : |a * b| = |a| * |b|

abs_nonneg.{u_1} {α : Type u_1} [Lattice α] [AddGroup α]
  [CovariantClass α α (fun x x_1 => x + x_1) fun x x_1 => x ≤ x_1]
  [CovariantClass α α (Function.swap fun x x_1 => x + x_1) fun x x_1 => x ≤ x_1]
  (a : α) : 0 ≤ |a|

by_contra zzh。设目标为A，它会将¬A作为一条假设，命名为zzh,把目标变为"false"。

change tgt' will change the goal from tgt to tgt', assuming these are definitionally equal.

change t' at h will change hypothesis h : t to have type t', assuming assuming t and t' are
  definitionally equal.

le_max_left.{u} {α : Type u} [LinearOrder α] (a b : α) : a ≤ max a b

le_max_right.{u} {α : Type u} [LinearOrder α] (a b : α) : b ≤ max a b

rw（rewrite）战术在 Lean 中只能用于等式的变换。

lt_irrefl.{u} {α : Type u} [Preorder α] (a : α) : ¬a < a

Real.sqrt_div {x : ℝ} (hx : 0 ≤ x) (y : ℝ) : √(x / y) = √x / √y

Real.sqrt_div' (x : ℝ) {y : ℝ} (hy : 0 ≤ y) : √(x / y) = √x / √y

div_mul_eq_mul_div.{u_1} {α : Type u_1} [DivisionCommMonoid α] (a b c : α) :
  a / b * c = a * c / b

Real.rpow_mul {x : ℝ} (hx : 0 ≤ x) (y z : ℝ) : x ^ (y * z) = (x ^ y) ^ z

Set.subset_def.{u} {α : Type u} {s t : Set α} : (s ⊆ t) = ∀ x ∈ s, x ∈ t

Set.inter_def.{u} {α : Type u} {s₁ s₂ : Set α} : s₁ ∩ s₂ = {a | a ∈ s₁ ∧ a ∈ s₂}

Set.mem_setOf.{u} {α : Type u} {a : α} {p : α → Prop} : a ∈ {x | p x} ↔ p a

Set.mem_inter_iff.{u} {α : Type u} (x : α) (a b : Set α) : x ∈ a ∩ b ↔ x ∈ a ∧ x ∈ b

The rintro tactic is a combination of the intros tactic with rcases to allow for
  destructuring patterns while introducing variables. See rcases for a description
  of supported patterns. For example, rintro (a | ⟨b, c⟩) ⟨d, e⟩ will introduce two
  variables, and then do case splits on both of them producing two subgoals, one
  with variables a d e and the other with b c d e.

Or.inl {a b : Prop} (h : a) : a ∨ b

Or.inr {a b : Prop} (h : b) : a ∨ b

exact P ¬P可以用于证明"false"目标。

not_or {p q : Prop} : ¬(p ∨ q) ↔ ¬p ∧ ¬q

not_and {a b : Prop} : ¬(a ∧ b) ↔ a → ¬b

apply 一个定理 at 一个假设。用于改写假设的形式。

and_comm {a b : Prop} : a ∧ b ↔ b ∧ a

Set.Subset.antisymm.{u} {α : Type u} {a b : Set α} (h₁ : a ⊆ b) (h₂ : b ⊆ a) : a = b

by_cases 假设名(比如h) : p。分两类讨论，第一类中引入了假设h : p，第二类中引入了假设h : ¬ p。

Real.rpow_intCast_mul {x : ℝ} (hx : 0 ≤ x) (n : ℤ) (z : ℝ) : x ^ (↑n * z) = (x ^ n) ^ z

Real.rpow_natCast_mul {x : ℝ} (hx : 0 ≤ x) (n : ℕ) (z : ℝ) : x ^ (↑n * z) = (x ^ n) ^ z

Real.sqrt_mul_self {x : ℝ} (h : 0 ≤ x) : √(x * x) = x

Real.sqrt_mul {x : ℝ} (hx : 0 ≤ x) (y : ℝ) : √(x * y) = √x * √y

Real.sqrt_mul' (x : ℝ) {y : ℝ} (hy : 0 ≤ y) : √(x * y) = √x * √y

Real.sqrt_sq {x : ℝ} (h : 0 ≤ x) : √(x ^ 2) = x

Nat.not_even_iff_odd {n : ℕ} : ¬Even n ↔ Odd n

Classical.em (p : Prop) : p ∨ ¬p

False.elim.{u} {C : Sort u} (h : False) : C。It says that from False, any
  desired proposition C holds.

Iff.symm {a b : Prop} (h : a ↔ b) : b ↔ a

assumption 用于解决那些可以直接从现有假设中得出的目标。Lean 会自动检查当前的假设列表，
  看看是否能找到一个直接满足当前目标的假设。

Set.mem_iUnion.{u, v} {α : Type u} {ι : Sort v} {x : α} {s : ι → Set α} :
  x ∈ ⋃ i, s i ↔ ∃ i, x ∈ s i

Set.mem_iInter.{u, v} {α : Type u} {ι : Sort v} {x : α} {s : ι → Set α} :
  x ∈ ⋂ i, s i ↔ ∀ (i : ι), x ∈ s i

specialize h a₁ ... aₙ。作用于假设h。该假设的前提条件（要么是全称量化，要么是非依赖的蕴含）
  会通过来自参数 a₁ ... aₙ 的具体项来实例化。这个战术会添加一个新的假设，形式为 h := h a₁ ...
  aₙ，并清除之前的假设。

contrapose。它turns a goal P → Q into ¬ Q → ¬ P。

Nat.exists_prime_and_dvd {n : ℕ} (hn : n ≠ 1) : ∃ p, Nat.Prime p ∧ p ∣ n

Set.eq_univ_of_forall.{u} {α : Type u} {s : Set α} : (∀ (x : α), x ∈ s) → s = univ

当目标为A∧B，假设中有h:A时，使用use h，会把目标变为B。这样就不用先constructor再使用h了。

在Lean 4中，prod l 表示列表 l 中所有元素的乘积。

Perm l₁ l₂ (或 l₁ ~ l₂) 表示列表 l₁ 和 l₂ 是彼此的排列，也就是说，l₁ 是通过 l₂ 的元素重新
  排序得到的。

congr：Apply congruence (recursively) to goals of the form ⊢ f as = f bs and
  ⊢ HEq (f as) (f bs). The optional parameter is the depth of the recursive applications.
  This is useful when congr is too aggressive in breaking down the goal. For example,
  given ⊢ f (g (x + y)) = f (g (y + x)), congr produces the goals ⊢ x = y and ⊢ y = x,
  while congr 2 produces the intended ⊢ x + y = y + x.当然,congr 1更保守。

ring：Tactic for evaluating expressions in commutative (semi)rings, allowing for
  variables in the exponent. If the goal is not appropriate for ring (e.g. not an
  equality) ring_nf will be suggested.

  ring! will use a more aggressive reducibility setting to determine equality of atoms.
  ring1 fails if the target is not an equality.
  For example:

  example (n : ℕ) (m : ℤ) : 2^(n+1) * m = 2 * 2^n * m := by ring
  example (a b : ℤ) (n : ℕ) : (a + b)^(n + 2) = (a^2 + b^2 + a * b + b * a) *
    (a + b)^n := by ring
  example (x y : ℕ) : x + id y = y + id x := by ring!
  example (x : ℕ) (h : x * 2 > 5): x + x > 5 := by ring; assumption -- suggests ring_nf
  ring不能直接化简像x^2*x⁻¹这样的表达式，因为 ring 战术只处理环结构中的多项式表达式，
  而不涉及倒数或除法。

norm_num：Normalize numerical expressions. Supports the operations + - * / ⁻¹ ^ and %
  over numerical types such as ℕ, ℤ, ℚ, ℝ, ℂ and some general algebraic types, and
  can prove goals of the form A = B, A ≠ B, A < B and A ≤ B, where A and B are
  numerical expressions. It also has a relatively simple primality prover.
  可以用于把x^1化简为x。
  可以用at简化假设。

linear_combination:it attempts to simplify the target by creating a linear combination of
  a list of equalities and subtracting it from the target. The tactic will create
  a linear combination by adding the equalities together from left to right, so
  the order of the input hypotheses does matter. If the normalize field of the
  configuration is set to false, then the tactic will simply set the user up to
  prove their target using the linear combination instead of normalizing the subtraction.

  Note: The left and right sides of all the equalities should have the same type,
  and the coefficients（系数） should also have this type. There must be instances of Mul
  and AddGroup for this type.

  The input e in linear_combination e is a linear combination of proofs of equalities,
  given as a sum/difference of coefficients multiplied by expressions. The coefficients
  may be arbitrary expressions. The expressions can be arbitrary proof terms proving
  equalities. Most commonly they are hypothesis names h1, h2, ....
  linear_combination (norm := tac) e runs the "normalization tactic" tac on the
  subgoal(s) after constructing the linear combination.
  The default normalization tactic is ring1, which closes the goal or fails.
  To get a subgoal in the case that it is not immediately provable, use ring_nf as
  the normalization tactic.
  To avoid normalization entirely, use skip as the normalization tactic.
  linear_combination (exp := n) e will take the goal to the nth power before
  subtracting the combination e. In other words, if the goal is t1 = t2,
  linear_combination (exp := n) e will change the goal to (t1 - t2)^n = 0
  before proceeding as above. This feature is not supported for linear_combination2.
  linear_combination2 e is the same as linear_combination e but it produces two
  subgoals instead of one: rather than proving that (a - b) - (a' - b') = 0 where
  a' = b' is the linear combination from e and a = b is the goal, it instead
  attempts to prove a = a' and b = b'. Because it does not use subtraction, this
  form is applicable also to semirings.
  Note that a goal which is provable by linear_combination e may not be provable
  by linear_combination2 e; in general you may need to add a coefficient to e to
  make both sides match, as in linear_combination2 e + c.
  You can also reverse equalities using ← h, so for example if h₁ : a = b then
  2 * (← h) is a proof of 2 * b = 2 * a.
  Example Usage:

  example (x y : ℤ) (h1 : x*y + 2*x = 1) (h2 : x = y) : x*y = -2*y + 1 := by
    linear_combination 1*h1 - 2*h2

  example (x y : ℤ) (h1 : x*y + 2*x = 1) (h2 : x = y) : x*y = -2*y + 1 := by
    linear_combination h1 - 2*h2

  example (x y : ℤ) (h1 : x*y + 2*x = 1) (h2 : x = y) : x*y = -2*y + 1 := by
    linear_combination (norm := ring_nf) -2*h2
    /- Goal: x * y + x * 2 - 1 = 0 -/

  example (x y z : ℝ) (ha : x + 2*y - z = 4) (hb : 2*x + y + z = -2)
      (hc : x + 2*y + z = 2) :
      -3*x - 3*y - 4*z = 2 := by
    linear_combination ha - hb - 2*hc

  example (x y : ℚ) (h1 : x + y = 3) (h2 : 3*x = 7) :
      x*x*y + y*x*y + 6*x = 3*x*y + 14 := by
    linear_combination x*y*h1 + 2*h2

  example (x y : ℤ) (h1 : x = -3) (h2 : y = 10) : 2*x = -6 := by
    linear_combination (norm := skip) 2*h1
    simp

  axiom qc : ℚ
  axiom hqc : qc = 2*qc

  example (a b : ℚ) (h : ∀ p q : ℚ, p = q) : 3*a + qc = 3*b + 2*qc := by
    linear_combination 3 * h a b + hqc

polyrith:Attempts to prove polynomial equality goals through polynomial arithmetic on
  the hypotheses (and additional proof terms if the user specifies them). It proves
  the goal by generating an appropriate call to the tactic linear_combination(这句话真
  是关键). If this call succeeds, the call to linear_combination is suggested to the user.

  polyrith will use all relevant hypotheses in the local context.
  polyrith [t1, t2, t3] will add proof terms t1, t2, t3 to the local context.
  polyrith only [h1, h2, h3, t1, t2, t3] will use only local hypotheses h1, h2, h3, and
  proofs t1, t2, t3. It will ignore the rest of the local context.
  Notes:

  This tactic only works with a working internet connection, since it calls Sage using
  the SageCell web API at https://sagecell.sagemath.org/. Many thanks to the Sage team
  and organization for allowing this use.
  This tactic assumes that the user has python3 installed and available on the path.
  (Test by opening a terminal and executing python3 --version.) It also assumes that
  the requests library is installed: python3 -m pip install requests.
  Examples:

  example (x y : ℚ) (h1 : x*y + 2*x = 1) (h2 : x = y) :
      x*y = -2*y + 1 := by
    polyrith
  -- Try this: linear_combination h1 - 2 * h2

  example (x y z w : ℚ) (hzw : z = w) : x*z + 2*y*z = x*w + 2*y*w := by
    polyrith
  -- Try this: linear_combination (2 * y + x) * hzw

  constant scary : ∀ a b : ℚ, a + b = 0

  example (a b c d : ℚ) (h : a + b = 0) (h2: b + c = 0) : a + b + c + d = 0 := by
    polyrith only [scary c d, h]
  -- Try this: linear_combination scary c d + h

move_add：The tactic move_add rearranges summands（被加数） of expressions. Calling
  move_add [a, ← b, ...] matches a, b,... with summands in the main goal. It then
  moves a to the far right and b to the far left of each addition in which they appear.
  The side to which the summands are moved is determined by the presence or absence of
  the arrow ←.

  The inputs a, b,... can be any terms, also with underscores. The tactic uses the
  first "new" summand that unifies with each one of the given inputs.

  There is a multiplicative variant, called move_mul.

  There is also a general tactic for a "binary associative commutative operation":
  move_oper. In this case the syntax requires providing first a term whose head symbol
  is the operation. E.g. move_oper HAdd.hAdd [...] is the same as move_add, while
  move_oper Max.max [...] rearranges maxs.
  move_add这个战术非常有用，用于消除表达式两边的相同项。

add_left_inj.{u_3} {G : Type u_3} [Add G] [IsRightCancelAdd G] (a : G) {b c : G} :
  b + a = c + a ↔ b = c

add_right_inj.{u_3} {G : Type u_3} [Add G] [IsLeftCancelAdd G] (a : G) {b c : G} :
  a + b = a + c ↔ b = c

field_simp:

simp:可以用at简化假设。

要注意运算域，比如theorem lean_workbook_23191 (n : ℕ) : 6*n = (n+1)^3 + (n-1)^3 -
  n^3 - n^3  :=  by sorry。它是不成立的，因为在自然数运算中，0-1=0，所以n取0时，n-1=0,
  等式两边不相等。

pow_succ.{u_2} {M : Type u_2} [Monoid M] (a : M) (n : ℕ) : a ^ (n + 1) = a ^ n * a

pow_succ'.{u_2} {M : Type u_2} [Monoid M] (a : M) (n : ℕ) : a ^ (n + 1) = a * a ^ n

对于lean认为 实数/0=0的解释：https://xenaproject.wordpress.com/2020/07/05/
  division-by-zero-in-type-theory-a-faq/
  即：
  theorem tmp1 :(1:ℝ)/0=0:=by
    norm_num

Real.sq_sqrt {x : ℝ} (h : 0 ≤ x) : (√x) ^ 2 = x

Real.sqrt_sq {x : ℝ} (h : 0 ≤ x) : √(x ^ 2) = x

Real.sqrt是不可计算的。例如：
  #eval Real.sqrt 21。会报错：failed to compile definition, consider marking
  it as 'noncomputable' because it depends on 'Real.sqrt', and it does not
  have executable codeLean 4。这是因为很深的数学原因（不是简单因为浮点数不准确）。
  但可以用Float.sqrt来算近似值。

Real.mul_self_sqrt {x : ℝ} (h : 0 ≤ x) : √x * √x = x

Real.sqrt_eq_zero' {x : ℝ} : √x = 0 ↔ x ≤ 0。这个定理说明，实数域内，√负数=0。

The omega tactic, for resolving integer and natural linear arithmetic problems.
  It is not yet a full decision procedure (no "dark" or "grey" shadows), but should
  be effective on many problems.
  We handle hypotheses of the form x = y, x < y, x ≤ y, and k ∣ x for x y in Nat or
  Int (and k a literal), along with negations of these statements.
  We decompose the sides of the inequalities as linear combinations of atoms.
  If we encounter x / k or x % k for literal integers k we introduce new auxiliary
  variables and the relevant inequalities.
  On the first pass, we do not perform case splits on natural subtraction. If omega
  fails, we recursively perform a case split on a natural subtraction appearing in
  a hypothesis, and try again.

  The options
  omega (config :={ splitDisjunctions := true, splitNatSub := true, splitNatAbs := true,
    splitMinMax := true })
  can be used to:

  splitDisjunctions: split any disjunctions found in the context, if the problem is
  not otherwise solvable.
  splitNatSub: for each appearance of ((a - b : Nat) : Int), split on a ≤ b if necessary.
  splitNatAbs: for each appearance of Int.natAbs a, split on 0 ≤ a if necessary.
  splitMinMax: for each occurrence of min a b, split on min a b = a ∨ min a b = b
  Currently, all of these are on by default.

sq.{u_2} {M : Type u_2} [Monoid M] (a : M) : a ^ 2 = a * a

theorem tmp2 (x y:ℝ):x ^ 2 * x⁻¹=x:=by

如何结束clac块？使用"_=目标:=?_",然后回到原来的块继续证明目标。这个非常好，增大了
  写proof的自由度。
  下面是一个例子：
  theorem lean_workbook_48007 (x y : ℝ) : 2 * (1 + x^2 * y^2) / (x * y) = 2 *
  (1 / (x * y) + x * y)  :=  by
    ring
    congr 2
    calc
      _=x ^ 2 * x⁻¹ * y ^ 2 * y⁻¹:=by ring
      _=x*y:=?_
    simp [sq]
    rw [mul_assoc]
    simp [sq]

Real.rpow_logb {b x : ℝ} (b_pos : 0 < b) (b_ne_one : b ≠ 1) (hx : 0 < x) :
  b ^ Real.logb b x = x

NNReal表示非负的实数集合。`ENNReal` 通过扩展 `Option NNReal` 实现：
  - **`NNReal`** （非负实数）表示所有的有限值 \([0, \infty)\)；
  - 额外增加一个 `none` 值，表示 \(+\infty\)。




\[
\text{ENNReal.ofReal}\  x =
\begin{cases} 
x, & \text{如果 } x \geq 0 \\ 
0, & \text{如果 } x < 0
\end{cases}
\]


SubderivAt f x表示函数f在点x的次梯度集合。

`LipschitzWith G f` 表示函数 \( f \) 是 **Lipschitz 连续的**，并且其 **Lipschitz 常数** 是 \( G \)。
