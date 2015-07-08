(get-info :version)
; (:version "4.3.2")
; Input file is <unknown>
; Started: 2015-07-08 11:21:00
; Silicon.buildVersion: 0.1-SNAPSHOT 63ede832faec+ default 2015/06/10 17:01:42
; ------------------------------------------------------------
; Preamble start
; 
; ; /z3config.smt2
(set-option :print-success true) ; Boogie: false
(set-option :global-decls true) ; Boogie: default
(set-option :auto_config false) ; Usually a good idea
(set-option :smt.mbqi false)
(set-option :model.v2 true)
(set-option :smt.phase_selection 0)
(set-option :smt.restart_strategy 0)
(set-option :smt.restart_factor |1.5|)
(set-option :smt.arith.random_initial_value true)
(set-option :smt.case_split 3)
(set-option :smt.delay_units true)
(set-option :smt.delay_units_threshold 16)
(set-option :nnf.sk_hack true)
(set-option :smt.qi.eager_threshold 100)
(set-option :smt.qi.cost "(+ weight generation)")
(set-option :type_check true)
(set-option :smt.bv.reflect true)
(set-option :smt.soft_timeout 30000)
; 
; ; /preamble.smt2
(declare-datatypes () ((
    $Snap $Snap.unit
    ($Snap.combine ($Snap.first $Snap) ($Snap.second $Snap)))))
(declare-sort $Ref)
(declare-const $Ref.null $Ref)
(define-sort $Perm () Real)
(define-const $Perm.Write $Perm 1.0)
(define-const $Perm.No $Perm 0.0)
(define-fun $Perm.isValidVar ((p $Perm)) Bool
	(<= $Perm.No p))
(define-fun $Perm.isReadVar ((p $Perm) (ub $Perm)) Bool
    (and ($Perm.isValidVar p)
         (not (= p $Perm.No))
         (< p $Perm.Write)))
(define-fun $Perm.min ((p1 $Perm) (p2 $Perm)) Real
    (ite (<= p1 p2) p1 p2))
(define-fun $Math.min ((a Int) (b Int)) Int
    (ite (<= a b) a b))
(define-fun $Math.clip ((a Int)) Int
    (ite (< a 0) 0 a))
(push) ; 1
(declare-sort $Seq<$Ref>)
(declare-sort $Set<Int>)
(declare-sort $Set<$Seq<$Ref>>)
(declare-sort $Set<Bool>)
(declare-sort $Set<$Ref>)
(declare-sort $FVF<$Ref>)
(declare-sort $FVF<$Seq<$Ref>>)
(declare-sort $FVF<Bool>)
(declare-sort $FVF<Int>)
; /dafny_axioms/sets_declarations_dafny.smt2 [Int]
(declare-fun $Set.in (Int $Set<Int>) Bool)
(declare-fun $Set.card ($Set<Int>) Int)
(declare-fun $Set.empty<Int> () $Set<Int>)
(declare-fun $Set.singleton (Int) $Set<Int>)
(declare-fun $Set.unionone ($Set<Int> Int) $Set<Int>)
(declare-fun $Set.union ($Set<Int> $Set<Int>) $Set<Int>)
(declare-fun $Set.disjoint ($Set<Int> $Set<Int>) Bool)
(declare-fun $Set.difference ($Set<Int> $Set<Int>) $Set<Int>)
(declare-fun $Set.intersection ($Set<Int> $Set<Int>) $Set<Int>)
(declare-fun $Set.subset ($Set<Int> $Set<Int>) Bool)
(declare-fun $Set.equal ($Set<Int> $Set<Int>) Bool)
; /dafny_axioms/sets_declarations_dafny.smt2 [Seq[Ref]]
(declare-fun $Set.in ($Seq<$Ref> $Set<$Seq<$Ref>>) Bool)
(declare-fun $Set.card ($Set<$Seq<$Ref>>) Int)
(declare-fun $Set.empty<$Seq<$Ref>> () $Set<$Seq<$Ref>>)
(declare-fun $Set.singleton ($Seq<$Ref>) $Set<$Seq<$Ref>>)
(declare-fun $Set.unionone ($Set<$Seq<$Ref>> $Seq<$Ref>) $Set<$Seq<$Ref>>)
(declare-fun $Set.union ($Set<$Seq<$Ref>> $Set<$Seq<$Ref>>) $Set<$Seq<$Ref>>)
(declare-fun $Set.disjoint ($Set<$Seq<$Ref>> $Set<$Seq<$Ref>>) Bool)
(declare-fun $Set.difference ($Set<$Seq<$Ref>> $Set<$Seq<$Ref>>) $Set<$Seq<$Ref>>)
(declare-fun $Set.intersection ($Set<$Seq<$Ref>> $Set<$Seq<$Ref>>) $Set<$Seq<$Ref>>)
(declare-fun $Set.subset ($Set<$Seq<$Ref>> $Set<$Seq<$Ref>>) Bool)
(declare-fun $Set.equal ($Set<$Seq<$Ref>> $Set<$Seq<$Ref>>) Bool)
; /dafny_axioms/sets_declarations_dafny.smt2 [Bool]
(declare-fun $Set.in (Bool $Set<Bool>) Bool)
(declare-fun $Set.card ($Set<Bool>) Int)
(declare-fun $Set.empty<Bool> () $Set<Bool>)
(declare-fun $Set.singleton (Bool) $Set<Bool>)
(declare-fun $Set.unionone ($Set<Bool> Bool) $Set<Bool>)
(declare-fun $Set.union ($Set<Bool> $Set<Bool>) $Set<Bool>)
(declare-fun $Set.disjoint ($Set<Bool> $Set<Bool>) Bool)
(declare-fun $Set.difference ($Set<Bool> $Set<Bool>) $Set<Bool>)
(declare-fun $Set.intersection ($Set<Bool> $Set<Bool>) $Set<Bool>)
(declare-fun $Set.subset ($Set<Bool> $Set<Bool>) Bool)
(declare-fun $Set.equal ($Set<Bool> $Set<Bool>) Bool)
; /dafny_axioms/sets_declarations_dafny.smt2 [Ref]
(declare-fun $Set.in ($Ref $Set<$Ref>) Bool)
(declare-fun $Set.card ($Set<$Ref>) Int)
(declare-fun $Set.empty<$Ref> () $Set<$Ref>)
(declare-fun $Set.singleton ($Ref) $Set<$Ref>)
(declare-fun $Set.unionone ($Set<$Ref> $Ref) $Set<$Ref>)
(declare-fun $Set.union ($Set<$Ref> $Set<$Ref>) $Set<$Ref>)
(declare-fun $Set.disjoint ($Set<$Ref> $Set<$Ref>) Bool)
(declare-fun $Set.difference ($Set<$Ref> $Set<$Ref>) $Set<$Ref>)
(declare-fun $Set.intersection ($Set<$Ref> $Set<$Ref>) $Set<$Ref>)
(declare-fun $Set.subset ($Set<$Ref> $Set<$Ref>) Bool)
(declare-fun $Set.equal ($Set<$Ref> $Set<$Ref>) Bool)
; /dafny_axioms/sequences_declarations_dafny.smt2 [Ref]
(declare-fun $Seq.length ($Seq<$Ref>) Int)
(declare-fun $Seq.empty<$Ref> () $Seq<$Ref>)
(declare-fun $Seq.singleton ($Ref) $Seq<$Ref>)
(declare-fun $Seq.build ($Seq<$Ref> $Ref) $Seq<$Ref>)
(declare-fun $Seq.index ($Seq<$Ref> Int) $Ref)
(declare-fun $Seq.append ($Seq<$Ref> $Seq<$Ref>) $Seq<$Ref>)
(declare-fun $Seq.update ($Seq<$Ref> Int $Ref) $Seq<$Ref>)
(declare-fun $Seq.contains ($Seq<$Ref> $Ref) Bool)
(declare-fun $Seq.take ($Seq<$Ref> Int) $Seq<$Ref>)
(declare-fun $Seq.drop ($Seq<$Ref> Int) $Seq<$Ref>)
(declare-fun $Seq.equal ($Seq<$Ref> $Seq<$Ref>) Bool)
(declare-fun $Seq.sameuntil ($Seq<$Ref> $Seq<$Ref> Int) Bool)
(assert true)
; /field_value_functions_declarations.smt2 [Set__contents: Seq[Ref]]
(declare-fun $FVF.domain_Set__contents ($FVF<$Seq<$Ref>>) $Set<$Ref>)
(declare-fun $FVF.lookup_Set__contents ($FVF<$Seq<$Ref>> $Ref) $Seq<$Ref>)
; /field_value_functions_declarations.smt2 [Ref__Boolean_value: Bool]
(declare-fun $FVF.domain_Ref__Boolean_value ($FVF<Bool>) $Set<$Ref>)
(declare-fun $FVF.lookup_Ref__Boolean_value ($FVF<Bool> $Ref) Bool)
; /field_value_functions_declarations.smt2 [Set__max: Int]
(declare-fun $FVF.domain_Set__max ($FVF<Int>) $Set<$Ref>)
(declare-fun $FVF.lookup_Set__max ($FVF<Int> $Ref) Int)
; /dafny_axioms/sequences_axioms_dafny.smt2 [Ref]
(assert (forall ((s $Seq<$Ref>) ) (! (<= 0 ($Seq.length s))
  :pattern ( ($Seq.length s))
  )))
(assert (= ($Seq.length $Seq.empty<$Ref>) 0))
(assert (forall ((s $Seq<$Ref>) ) (! (=> (= ($Seq.length s) 0) (= s $Seq.empty<$Ref>))
  :pattern ( ($Seq.length s))
  )))
(assert (forall ((t $Ref) ) (! (= ($Seq.length ($Seq.singleton t)) 1)
  :pattern ( ($Seq.length ($Seq.singleton t)))
  )))
(assert (forall ((s $Seq<$Ref>) (v $Ref) ) (! (= ($Seq.length ($Seq.build s v)) (+ 1 ($Seq.length s)))
  :pattern ( ($Seq.length ($Seq.build s v)))
  )))
(assert (forall ((s $Seq<$Ref>) (i Int) (v $Ref) ) (! (and
  (=> (= i ($Seq.length s)) (= ($Seq.index ($Seq.build s v) i) v))
  (=> (not (= i ($Seq.length s))) (= ($Seq.index ($Seq.build s v) i) ($Seq.index s i))))
  :pattern ( ($Seq.index ($Seq.build s v) i))
  )))
(assert (forall ((s0 $Seq<$Ref>) (s1 $Seq<$Ref>) ) (! (= ($Seq.length ($Seq.append s0 s1)) (+ ($Seq.length s0) ($Seq.length s1)))
  :pattern ( ($Seq.length ($Seq.append s0 s1)))
  )))
(assert (forall ((t $Ref) ) (! (= ($Seq.index ($Seq.singleton t) 0) t)
  :pattern ( ($Seq.index ($Seq.singleton t) 0))
  )))
(assert (forall ((s0 $Seq<$Ref>) (s1 $Seq<$Ref>) (n Int) ) (! (and
  (=> (< n ($Seq.length s0)) (= ($Seq.index ($Seq.append s0 s1) n) ($Seq.index s0 n)))
  (=> (<= ($Seq.length s0) n) (= ($Seq.index ($Seq.append s0 s1) n) ($Seq.index s1 (- n ($Seq.length s0))))))
  :pattern ( ($Seq.index ($Seq.append s0 s1) n))
  )))
(assert (forall ((s $Seq<$Ref>) (i Int) (v $Ref) ) (! (=> (and
  (<= 0 i)
  (< i ($Seq.length s))) (= ($Seq.length ($Seq.update s i v)) ($Seq.length s)))
  :pattern ( ($Seq.length ($Seq.update s i v)))
  )))
(assert (forall ((s $Seq<$Ref>) (i Int) (v $Ref) (n Int) ) (! (=> (and
  (<= 0 n)
  (< n ($Seq.length s))) (and
  (=> (= i n) (= ($Seq.index ($Seq.update s i v) n) v))
  (=> (not (= i n)) (= ($Seq.index ($Seq.update s i v) n) ($Seq.index s n)))))
  :pattern ( ($Seq.index ($Seq.update s i v) n))
  )))
(assert (forall ((s $Seq<$Ref>) (x $Ref) ) (!
  (and
    (=>
      ($Seq.contains s x)
      (exists ((i Int) ) (!
        (and
          (<= 0 i)
          (< i ($Seq.length s))
          (= ($Seq.index s i) x))
      :pattern ( ($Seq.index s i))
      )))
    (=>
      (exists ((i Int) ) (!
        (and
          (<= 0 i)
          (< i ($Seq.length s))
          (= ($Seq.index s i) x))
        :pattern ( ($Seq.index s i))
      ))
      ($Seq.contains s x)))
  :pattern ( ($Seq.contains s x))
  )))
(assert (forall ((x $Ref) ) (! (not ($Seq.contains $Seq.empty<$Ref> x))
  :pattern ( ($Seq.contains $Seq.empty<$Ref> x))
  )))
(assert (forall ((s0 $Seq<$Ref>) (s1 $Seq<$Ref>) (x $Ref) ) (! (and
  (=> ($Seq.contains ($Seq.append s0 s1) x) (or
  ($Seq.contains s0 x)
  ($Seq.contains s1 x)))
  (=> (or
  ($Seq.contains s0 x)
  ($Seq.contains s1 x)) ($Seq.contains ($Seq.append s0 s1) x)))
  :pattern ( ($Seq.contains ($Seq.append s0 s1) x))
  )))
(assert (forall ((s $Seq<$Ref>) (v $Ref) (x $Ref) ) (! (and
  (=> ($Seq.contains ($Seq.build s v) x) (or
  (= v x)
  ($Seq.contains s x)))
  (=> (or
  (= v x)
  ($Seq.contains s x)) ($Seq.contains ($Seq.build s v) x)))
  :pattern ( ($Seq.contains ($Seq.build s v) x))
  )))
(assert (forall ((s $Seq<$Ref>) (n Int) (x $Ref) ) (!
  (and
    (=>
      ($Seq.contains ($Seq.take s n) x)
      (exists ((i Int) ) (!
        (and
          (<= 0 i)
          (< i n)
          (< i ($Seq.length s))
          (= ($Seq.index s i) x))
        :pattern ( ($Seq.index s i))
      )))
    (=>
      (exists ((i Int) ) (!
        (and
          (<= 0 i)
          (< i n)
          (< i ($Seq.length s))
          (= ($Seq.index s i) x))
        :pattern ( ($Seq.index s i))
      ))
      ($Seq.contains ($Seq.take s n) x)))
  :pattern ( ($Seq.contains ($Seq.take s n) x))
  )))
(assert (forall ((s $Seq<$Ref>) (n Int) (x $Ref) ) (!
  (and
    (=>
      ($Seq.contains ($Seq.drop s n) x)
      (exists ((i Int) ) (!
        (and
          (<= 0 n)
          (<= n i)
          (< i ($Seq.length s))
          (= ($Seq.index s i) x))
        :pattern ( ($Seq.index s i))
      )))
    (=>
      (exists ((i Int) ) (!
        (and
          (<= 0 n)
          (<= n i)
          (< i ($Seq.length s))
          (= ($Seq.index s i) x))
        :pattern ( ($Seq.index s i))
      ))
      ($Seq.contains ($Seq.drop s n) x)))
  :pattern ( ($Seq.contains ($Seq.drop s n) x))
  )))
(assert (forall ((s0 $Seq<$Ref>) (s1 $Seq<$Ref>) ) (! (and
  (=> ($Seq.equal s0 s1) (and
  (= ($Seq.length s0) ($Seq.length s1))
  (forall ((j Int) ) (! (=> (and
  (<= 0 j)
  (< j ($Seq.length s0))) (= ($Seq.index s0 j) ($Seq.index s1 j)))
  :pattern ( ($Seq.index s0 j))
  :pattern ( ($Seq.index s1 j))
  ))))
  (=> (and
  (= ($Seq.length s0) ($Seq.length s1))
  (forall ((j Int) ) (! (=> (and
  (<= 0 j)
  (< j ($Seq.length s0))) (= ($Seq.index s0 j) ($Seq.index s1 j)))
  :pattern ( ($Seq.index s0 j))
  :pattern ( ($Seq.index s1 j))
  ))) ($Seq.equal s0 s1)))
  :pattern ( ($Seq.equal s0 s1))
  )))
(assert (forall ((a $Seq<$Ref>) (b $Seq<$Ref>) ) (! (=> ($Seq.equal a b) (= a b))
  :pattern ( ($Seq.equal a b))
  )))
(assert (forall ((s0 $Seq<$Ref>) (s1 $Seq<$Ref>) (n Int) ) (! (and
  (=> ($Seq.sameuntil s0 s1 n) (forall ((j Int) ) (! (=> (and
  (<= 0 j)
  (< j n)) (= ($Seq.index s0 j) ($Seq.index s1 j)))
  :pattern ( ($Seq.index s0 j))
  :pattern ( ($Seq.index s1 j))
  )))
  (=> (forall ((j Int) ) (! (=> (and
  (<= 0 j)
  (< j n)) (= ($Seq.index s0 j) ($Seq.index s1 j)))
  :pattern ( ($Seq.index s0 j))
  :pattern ( ($Seq.index s1 j))
  )) ($Seq.sameuntil s0 s1 n)))
  :pattern ( ($Seq.sameuntil s0 s1 n))
  )))
(assert (forall ((s $Seq<$Ref>) (n Int) ) (! (=> (<= 0 n) (and
  (=> (<= n ($Seq.length s)) (= ($Seq.length ($Seq.take s n)) n))
  (=> (< ($Seq.length s) n) (= ($Seq.length ($Seq.take s n)) ($Seq.length s)))))
  :pattern ( ($Seq.length ($Seq.take s n)))
  )))
(assert (forall ((s $Seq<$Ref>) (n Int) (j Int) ) (! (=> (and
  (<= 0 j)
  (< j n)
  (< j ($Seq.length s))) (= ($Seq.index ($Seq.take s n) j) ($Seq.index s j)))
  :pattern ( ($Seq.index ($Seq.take s n) j))
  )))
(assert (forall ((s $Seq<$Ref>) (n Int) ) (! (=> (<= 0 n) (and
  (=> (<= n ($Seq.length s)) (= ($Seq.length ($Seq.drop s n)) (- ($Seq.length s) n)))
  (=> (< ($Seq.length s) n) (= ($Seq.length ($Seq.drop s n)) 0))))
  :pattern ( ($Seq.length ($Seq.drop s n)))
  )))
(assert (forall ((s $Seq<$Ref>) (n Int) (j Int) ) (! (=> (and
  (<= 0 n)
  (<= 0 j)
  (< j (- ($Seq.length s) n))) (= ($Seq.index ($Seq.drop s n) j) ($Seq.index s (+ j n))))
  :pattern ( ($Seq.index ($Seq.drop s n) j))
  )))
(assert (forall ((s $Seq<$Ref>) (i Int) (v $Ref) (n Int) ) (! (=> (and
  (<= 0 i)
  (< i n)
  (<= n ($Seq.length s))) (= ($Seq.take ($Seq.update s i v) n) ($Seq.update ($Seq.take s n) i v)))
  :pattern ( ($Seq.take ($Seq.update s i v) n))
  )))
(assert (forall ((s $Seq<$Ref>) (i Int) (v $Ref) (n Int) ) (! (=> (and
  (<= n i)
  (< i ($Seq.length s))) (= ($Seq.take ($Seq.update s i v) n) ($Seq.take s n)))
  :pattern ( ($Seq.take ($Seq.update s i v) n))
  )))
(assert (forall ((s $Seq<$Ref>) (i Int) (v $Ref) (n Int) ) (! (=> (and
  (<= 0 n)
  (<= n i)
  (< i ($Seq.length s))) (= ($Seq.drop ($Seq.update s i v) n) ($Seq.update ($Seq.drop s n) (- i n) v)))
  :pattern ( ($Seq.drop ($Seq.update s i v) n))
  )))
(assert (forall ((s $Seq<$Ref>) (i Int) (v $Ref) (n Int) ) (! (=> (and
  (<= 0 i)
  (< i n)
  (< n ($Seq.length s))) (= ($Seq.drop ($Seq.update s i v) n) ($Seq.drop s n)))
  :pattern ( ($Seq.drop ($Seq.update s i v) n))
  )))
(assert (forall ((s $Seq<$Ref>) (v $Ref) (n Int) ) (! (=> (and
  (<= 0 n)
  (<= n ($Seq.length s))) (= ($Seq.drop ($Seq.build s v) n) ($Seq.build ($Seq.drop s n) v)))
  :pattern ( ($Seq.drop ($Seq.build s v) n))
  )))
(assert (forall ((s $Seq<$Ref>) (n Int) ) (! (=> (= n 0) (= ($Seq.drop s n) s))
  :pattern ( ($Seq.drop s n))
  )))
(assert (forall ((s $Seq<$Ref>) (n Int) ) (! (=> (= n 0) (= ($Seq.take s n) $Seq.empty<$Ref>))
  :pattern ( ($Seq.take s n))
  )))
(assert (forall ((s $Seq<$Ref>) (m Int) (n Int) ) (! (=> (and
  (<= 0 m)
  (<= 0 n)
  (<= (+ m n) ($Seq.length s))) (= ($Seq.drop ($Seq.drop s m) n) ($Seq.drop s (+ m n))))
  :pattern ( ($Seq.drop ($Seq.drop s m) n))
  )))
(assert (forall ((x $Ref) (y $Ref)) (!
  (iff
    ($Seq.contains ($Seq.singleton x) y)
    (= x y))
  :pattern (($Seq.contains ($Seq.singleton x) y))
  )))
; /dafny_axioms/sets_axioms_dafny.smt2 [Int]
(assert (forall ((s $Set<Int>)) (!
  (<= 0 ($Set.card s))
  :pattern (($Set.card s))
  )))
(assert (forall ((o Int)) (!
  (not ($Set.in o $Set.empty<Int>))
  :pattern (($Set.in o $Set.empty<Int>))
  )))
(assert (forall ((s $Set<Int>)) (!
  (and
    (iff
      (= ($Set.card s) 0)
      (= s $Set.empty<Int>))
    (implies
      (not (= ($Set.card s) 0))
      (exists ((x Int)) (!
        ($Set.in x s)
        :pattern (($Set.in x s))
      ))))
  :pattern (($Set.card s))
  )))
(assert (forall ((r Int)) (!
  ($Set.in r ($Set.singleton r))
  :pattern (($Set.in r ($Set.singleton r)))
  )))
(assert (forall ((r Int) (o Int)) (!
  (iff
    ($Set.in o ($Set.singleton r))
    (= r o))
  :pattern (($Set.in o ($Set.singleton r)))
  )))
(assert (forall ((r Int)) (!
  (= ($Set.card ($Set.singleton r)) 1)
  :pattern (($Set.card ($Set.singleton r)))
  )))
(assert (forall ((a $Set<Int>) (x Int) (o Int)) (!
  (iff
    ($Set.in o ($Set.unionone a x))
    (or
      (= o x)
      ($Set.in o a)))
  :pattern (($Set.in o ($Set.unionone a x)))
  )))
(assert (forall ((a $Set<Int>) (x Int)) (!
  ($Set.in x ($Set.unionone a x))
  :pattern (($Set.in x ($Set.unionone a x)))
  )))
(assert (forall ((a $Set<Int>) (x Int) (y Int)) (!
  (=>
    ($Set.in y a)
    ($Set.in y ($Set.unionone a x)))
  :pattern (($Set.in y a) ($Set.in y ($Set.unionone a x)))
  )))
(assert (forall ((a $Set<Int>) (x Int)) (!
  (=>
    ($Set.in x a)
    (= ($Set.card ($Set.unionone a x)) ($Set.card a)))
  :pattern (($Set.card ($Set.unionone a x)))
  )))
(assert (forall ((a $Set<Int>) (x Int)) (!
  (=>
    (not ($Set.in x a))
    (= ($Set.card ($Set.unionone a x)) (+ ($Set.card a) 1)))
  :pattern (($Set.card ($Set.unionone a x)))
  )))
(assert (forall ((a $Set<Int>) (b $Set<Int>) (o Int)) (!
  (iff
    ($Set.in o ($Set.union a b))
    (or
      ($Set.in o a)
      ($Set.in o b)))
  :pattern (($Set.in o ($Set.union a b)))
  )))
(assert (forall ((a $Set<Int>) (b $Set<Int>) (y Int)) (!
  (=>
    ($Set.in y a)
    ($Set.in y ($Set.union a b)))
  :pattern (($Set.in y ($Set.union a b)) ($Set.in y a))
  )))
(assert (forall ((a $Set<Int>) (b $Set<Int>) (y Int)) (!
  (=>
    ($Set.in y b)
    ($Set.in y ($Set.union a b)))
  :pattern (($Set.in y ($Set.union a b)) ($Set.in y b))
  )))
(assert (forall ((a $Set<Int>) (b $Set<Int>) (o Int)) (!
  (iff
    ($Set.in o ($Set.intersection a b))
    (and
      ($Set.in o a)
      ($Set.in o b)))
  :pattern (($Set.in o ($Set.intersection a b)))
  )))
(assert (forall ((a $Set<Int>) (b $Set<Int>)) (!
  (=
    ($Set.union ($Set.union a b) b)
    ($Set.union a b))
  :pattern (($Set.union ($Set.union a b) b))
  )))
(assert (forall ((a $Set<Int>) (b $Set<Int>)) (!
  (=
    ($Set.union a ($Set.union a b))
    ($Set.union a b))
    :pattern (($Set.union a ($Set.union a b)))
  )))
(assert (forall ((a $Set<Int>) (b $Set<Int>)) (!
  (=
    ($Set.intersection ($Set.intersection a b) b)
    ($Set.intersection a b))
  :pattern (($Set.intersection ($Set.intersection a b) b))
  )))
(assert (forall ((a $Set<Int>) (b $Set<Int>)) (!
  (=
    ($Set.intersection a ($Set.intersection a b))
    ($Set.intersection a b))
  :pattern (($Set.intersection a ($Set.intersection a b)))
  )))
(assert (forall ((a $Set<Int>) (b $Set<Int>)) (!
  (=
    (+
      ($Set.card ($Set.union a b))
      ($Set.card ($Set.intersection a b)))
    (+
      ($Set.card a)
      ($Set.card b)))
  :pattern (($Set.card ($Set.union a b)))
  :pattern (($Set.card ($Set.intersection a b)))
  )))
(assert (forall ((a $Set<Int>) (b $Set<Int>) (o Int)) (!
  (iff
    ($Set.in o ($Set.difference a b))
    (and
      ($Set.in o a)
      (not ($Set.in o b))))
  :pattern (($Set.in o ($Set.difference a b)))
  )))
(assert (forall ((a $Set<Int>) (b $Set<Int>) (y Int)) (!
  (=>
    ($Set.in y b)
    (not ($Set.in y ($Set.difference a b))))
  :pattern (($Set.in y ($Set.difference a b)) ($Set.in y b))
  )))
(assert (forall ((a $Set<Int>) (b $Set<Int>)) (!
  (iff
    ($Set.subset a b)
    (forall ((o Int)) (!
      (=>
        ($Set.in o a)
        ($Set.in o b))
      :pattern (($Set.in o a))
      :pattern (($Set.in o b))
    )))
  :pattern (($Set.subset a b))
  )))
(assert (forall ((a $Set<Int>) (b $Set<Int>)) (!
  (iff
    ($Set.equal a b)
    (forall ((o Int)) (!
      (iff
        ($Set.in o a)
        ($Set.in o b))
      :pattern (($Set.in o a))
      :pattern (($Set.in o b))
      )))
  :pattern (($Set.equal a b))
  )))
(assert (forall ((a $Set<Int>) (b $Set<Int>)) (!
  (=>
    ($Set.equal a b)
    (= a b))
  :pattern (($Set.equal a b))
  )))
(assert (forall ((a $Set<Int>) (b $Set<Int>)) (!
  (iff
    ($Set.disjoint a b)
    (forall ((o Int)) (!
      (or
        (not ($Set.in o a))
        (not ($Set.in o b)))
      :pattern (($Set.in o a))
      :pattern (($Set.in o b))
      )))
  :pattern (($Set.disjoint a b))
  )))
(assert (forall ((a $Set<Int>) (b $Set<Int>)) (!
  (and
    (=
      (+
        (+
          ($Set.card ($Set.difference a b))
          ($Set.card ($Set.difference b a)))
        ($Set.card ($Set.intersection a b)))
      ($Set.card ($Set.union a b)))
    (=
      ($Set.card ($Set.difference a b))
      (-
        ($Set.card a)
        ($Set.card ($Set.intersection a b)))))
  :pattern (($Set.card ($Set.difference a b)) ($Set.card ($Set.intersection a b)))
  )))
; /dafny_axioms/sets_axioms_dafny.smt2 [Seq[Ref]]
(assert (forall ((s $Set<$Seq<$Ref>>)) (!
  (<= 0 ($Set.card s))
  :pattern (($Set.card s))
  )))
(assert (forall ((o $Seq<$Ref>)) (!
  (not ($Set.in o $Set.empty<$Seq<$Ref>>))
  :pattern (($Set.in o $Set.empty<$Seq<$Ref>>))
  )))
(assert (forall ((s $Set<$Seq<$Ref>>)) (!
  (and
    (iff
      (= ($Set.card s) 0)
      (= s $Set.empty<$Seq<$Ref>>))
    (implies
      (not (= ($Set.card s) 0))
      (exists ((x $Seq<$Ref>)) (!
        ($Set.in x s)
        :pattern (($Set.in x s))
      ))))
  :pattern (($Set.card s))
  )))
(assert (forall ((r $Seq<$Ref>)) (!
  ($Set.in r ($Set.singleton r))
  :pattern (($Set.in r ($Set.singleton r)))
  )))
(assert (forall ((r $Seq<$Ref>) (o $Seq<$Ref>)) (!
  (iff
    ($Set.in o ($Set.singleton r))
    (= r o))
  :pattern (($Set.in o ($Set.singleton r)))
  )))
(assert (forall ((r $Seq<$Ref>)) (!
  (= ($Set.card ($Set.singleton r)) 1)
  :pattern (($Set.card ($Set.singleton r)))
  )))
(assert (forall ((a $Set<$Seq<$Ref>>) (x $Seq<$Ref>) (o $Seq<$Ref>)) (!
  (iff
    ($Set.in o ($Set.unionone a x))
    (or
      (= o x)
      ($Set.in o a)))
  :pattern (($Set.in o ($Set.unionone a x)))
  )))
(assert (forall ((a $Set<$Seq<$Ref>>) (x $Seq<$Ref>)) (!
  ($Set.in x ($Set.unionone a x))
  :pattern (($Set.in x ($Set.unionone a x)))
  )))
(assert (forall ((a $Set<$Seq<$Ref>>) (x $Seq<$Ref>) (y $Seq<$Ref>)) (!
  (=>
    ($Set.in y a)
    ($Set.in y ($Set.unionone a x)))
  :pattern (($Set.in y a) ($Set.in y ($Set.unionone a x)))
  )))
(assert (forall ((a $Set<$Seq<$Ref>>) (x $Seq<$Ref>)) (!
  (=>
    ($Set.in x a)
    (= ($Set.card ($Set.unionone a x)) ($Set.card a)))
  :pattern (($Set.card ($Set.unionone a x)))
  )))
(assert (forall ((a $Set<$Seq<$Ref>>) (x $Seq<$Ref>)) (!
  (=>
    (not ($Set.in x a))
    (= ($Set.card ($Set.unionone a x)) (+ ($Set.card a) 1)))
  :pattern (($Set.card ($Set.unionone a x)))
  )))
(assert (forall ((a $Set<$Seq<$Ref>>) (b $Set<$Seq<$Ref>>) (o $Seq<$Ref>)) (!
  (iff
    ($Set.in o ($Set.union a b))
    (or
      ($Set.in o a)
      ($Set.in o b)))
  :pattern (($Set.in o ($Set.union a b)))
  )))
(assert (forall ((a $Set<$Seq<$Ref>>) (b $Set<$Seq<$Ref>>) (y $Seq<$Ref>)) (!
  (=>
    ($Set.in y a)
    ($Set.in y ($Set.union a b)))
  :pattern (($Set.in y ($Set.union a b)) ($Set.in y a))
  )))
(assert (forall ((a $Set<$Seq<$Ref>>) (b $Set<$Seq<$Ref>>) (y $Seq<$Ref>)) (!
  (=>
    ($Set.in y b)
    ($Set.in y ($Set.union a b)))
  :pattern (($Set.in y ($Set.union a b)) ($Set.in y b))
  )))
(assert (forall ((a $Set<$Seq<$Ref>>) (b $Set<$Seq<$Ref>>) (o $Seq<$Ref>)) (!
  (iff
    ($Set.in o ($Set.intersection a b))
    (and
      ($Set.in o a)
      ($Set.in o b)))
  :pattern (($Set.in o ($Set.intersection a b)))
  )))
(assert (forall ((a $Set<$Seq<$Ref>>) (b $Set<$Seq<$Ref>>)) (!
  (=
    ($Set.union ($Set.union a b) b)
    ($Set.union a b))
  :pattern (($Set.union ($Set.union a b) b))
  )))
(assert (forall ((a $Set<$Seq<$Ref>>) (b $Set<$Seq<$Ref>>)) (!
  (=
    ($Set.union a ($Set.union a b))
    ($Set.union a b))
    :pattern (($Set.union a ($Set.union a b)))
  )))
(assert (forall ((a $Set<$Seq<$Ref>>) (b $Set<$Seq<$Ref>>)) (!
  (=
    ($Set.intersection ($Set.intersection a b) b)
    ($Set.intersection a b))
  :pattern (($Set.intersection ($Set.intersection a b) b))
  )))
(assert (forall ((a $Set<$Seq<$Ref>>) (b $Set<$Seq<$Ref>>)) (!
  (=
    ($Set.intersection a ($Set.intersection a b))
    ($Set.intersection a b))
  :pattern (($Set.intersection a ($Set.intersection a b)))
  )))
(assert (forall ((a $Set<$Seq<$Ref>>) (b $Set<$Seq<$Ref>>)) (!
  (=
    (+
      ($Set.card ($Set.union a b))
      ($Set.card ($Set.intersection a b)))
    (+
      ($Set.card a)
      ($Set.card b)))
  :pattern (($Set.card ($Set.union a b)))
  :pattern (($Set.card ($Set.intersection a b)))
  )))
(assert (forall ((a $Set<$Seq<$Ref>>) (b $Set<$Seq<$Ref>>) (o $Seq<$Ref>)) (!
  (iff
    ($Set.in o ($Set.difference a b))
    (and
      ($Set.in o a)
      (not ($Set.in o b))))
  :pattern (($Set.in o ($Set.difference a b)))
  )))
(assert (forall ((a $Set<$Seq<$Ref>>) (b $Set<$Seq<$Ref>>) (y $Seq<$Ref>)) (!
  (=>
    ($Set.in y b)
    (not ($Set.in y ($Set.difference a b))))
  :pattern (($Set.in y ($Set.difference a b)) ($Set.in y b))
  )))
(assert (forall ((a $Set<$Seq<$Ref>>) (b $Set<$Seq<$Ref>>)) (!
  (iff
    ($Set.subset a b)
    (forall ((o $Seq<$Ref>)) (!
      (=>
        ($Set.in o a)
        ($Set.in o b))
      :pattern (($Set.in o a))
      :pattern (($Set.in o b))
    )))
  :pattern (($Set.subset a b))
  )))
(assert (forall ((a $Set<$Seq<$Ref>>) (b $Set<$Seq<$Ref>>)) (!
  (iff
    ($Set.equal a b)
    (forall ((o $Seq<$Ref>)) (!
      (iff
        ($Set.in o a)
        ($Set.in o b))
      :pattern (($Set.in o a))
      :pattern (($Set.in o b))
      )))
  :pattern (($Set.equal a b))
  )))
(assert (forall ((a $Set<$Seq<$Ref>>) (b $Set<$Seq<$Ref>>)) (!
  (=>
    ($Set.equal a b)
    (= a b))
  :pattern (($Set.equal a b))
  )))
(assert (forall ((a $Set<$Seq<$Ref>>) (b $Set<$Seq<$Ref>>)) (!
  (iff
    ($Set.disjoint a b)
    (forall ((o $Seq<$Ref>)) (!
      (or
        (not ($Set.in o a))
        (not ($Set.in o b)))
      :pattern (($Set.in o a))
      :pattern (($Set.in o b))
      )))
  :pattern (($Set.disjoint a b))
  )))
(assert (forall ((a $Set<$Seq<$Ref>>) (b $Set<$Seq<$Ref>>)) (!
  (and
    (=
      (+
        (+
          ($Set.card ($Set.difference a b))
          ($Set.card ($Set.difference b a)))
        ($Set.card ($Set.intersection a b)))
      ($Set.card ($Set.union a b)))
    (=
      ($Set.card ($Set.difference a b))
      (-
        ($Set.card a)
        ($Set.card ($Set.intersection a b)))))
  :pattern (($Set.card ($Set.difference a b)) ($Set.card ($Set.intersection a b)))
  )))
; /dafny_axioms/sets_axioms_dafny.smt2 [Bool]
(assert (forall ((s $Set<Bool>)) (!
  (<= 0 ($Set.card s))
  :pattern (($Set.card s))
  )))
(assert (forall ((o Bool)) (!
  (not ($Set.in o $Set.empty<Bool>))
  :pattern (($Set.in o $Set.empty<Bool>))
  )))
(assert (forall ((s $Set<Bool>)) (!
  (and
    (iff
      (= ($Set.card s) 0)
      (= s $Set.empty<Bool>))
    (implies
      (not (= ($Set.card s) 0))
      (exists ((x Bool)) (!
        ($Set.in x s)
        :pattern (($Set.in x s))
      ))))
  :pattern (($Set.card s))
  )))
(assert (forall ((r Bool)) (!
  ($Set.in r ($Set.singleton r))
  :pattern (($Set.in r ($Set.singleton r)))
  )))
(assert (forall ((r Bool) (o Bool)) (!
  (iff
    ($Set.in o ($Set.singleton r))
    (= r o))
  :pattern (($Set.in o ($Set.singleton r)))
  )))
(assert (forall ((r Bool)) (!
  (= ($Set.card ($Set.singleton r)) 1)
  :pattern (($Set.card ($Set.singleton r)))
  )))
(assert (forall ((a $Set<Bool>) (x Bool) (o Bool)) (!
  (iff
    ($Set.in o ($Set.unionone a x))
    (or
      (= o x)
      ($Set.in o a)))
  :pattern (($Set.in o ($Set.unionone a x)))
  )))
(assert (forall ((a $Set<Bool>) (x Bool)) (!
  ($Set.in x ($Set.unionone a x))
  :pattern (($Set.in x ($Set.unionone a x)))
  )))
(assert (forall ((a $Set<Bool>) (x Bool) (y Bool)) (!
  (=>
    ($Set.in y a)
    ($Set.in y ($Set.unionone a x)))
  :pattern (($Set.in y a) ($Set.in y ($Set.unionone a x)))
  )))
(assert (forall ((a $Set<Bool>) (x Bool)) (!
  (=>
    ($Set.in x a)
    (= ($Set.card ($Set.unionone a x)) ($Set.card a)))
  :pattern (($Set.card ($Set.unionone a x)))
  )))
(assert (forall ((a $Set<Bool>) (x Bool)) (!
  (=>
    (not ($Set.in x a))
    (= ($Set.card ($Set.unionone a x)) (+ ($Set.card a) 1)))
  :pattern (($Set.card ($Set.unionone a x)))
  )))
(assert (forall ((a $Set<Bool>) (b $Set<Bool>) (o Bool)) (!
  (iff
    ($Set.in o ($Set.union a b))
    (or
      ($Set.in o a)
      ($Set.in o b)))
  :pattern (($Set.in o ($Set.union a b)))
  )))
(assert (forall ((a $Set<Bool>) (b $Set<Bool>) (y Bool)) (!
  (=>
    ($Set.in y a)
    ($Set.in y ($Set.union a b)))
  :pattern (($Set.in y ($Set.union a b)) ($Set.in y a))
  )))
(assert (forall ((a $Set<Bool>) (b $Set<Bool>) (y Bool)) (!
  (=>
    ($Set.in y b)
    ($Set.in y ($Set.union a b)))
  :pattern (($Set.in y ($Set.union a b)) ($Set.in y b))
  )))
(assert (forall ((a $Set<Bool>) (b $Set<Bool>) (o Bool)) (!
  (iff
    ($Set.in o ($Set.intersection a b))
    (and
      ($Set.in o a)
      ($Set.in o b)))
  :pattern (($Set.in o ($Set.intersection a b)))
  )))
(assert (forall ((a $Set<Bool>) (b $Set<Bool>)) (!
  (=
    ($Set.union ($Set.union a b) b)
    ($Set.union a b))
  :pattern (($Set.union ($Set.union a b) b))
  )))
(assert (forall ((a $Set<Bool>) (b $Set<Bool>)) (!
  (=
    ($Set.union a ($Set.union a b))
    ($Set.union a b))
    :pattern (($Set.union a ($Set.union a b)))
  )))
(assert (forall ((a $Set<Bool>) (b $Set<Bool>)) (!
  (=
    ($Set.intersection ($Set.intersection a b) b)
    ($Set.intersection a b))
  :pattern (($Set.intersection ($Set.intersection a b) b))
  )))
(assert (forall ((a $Set<Bool>) (b $Set<Bool>)) (!
  (=
    ($Set.intersection a ($Set.intersection a b))
    ($Set.intersection a b))
  :pattern (($Set.intersection a ($Set.intersection a b)))
  )))
(assert (forall ((a $Set<Bool>) (b $Set<Bool>)) (!
  (=
    (+
      ($Set.card ($Set.union a b))
      ($Set.card ($Set.intersection a b)))
    (+
      ($Set.card a)
      ($Set.card b)))
  :pattern (($Set.card ($Set.union a b)))
  :pattern (($Set.card ($Set.intersection a b)))
  )))
(assert (forall ((a $Set<Bool>) (b $Set<Bool>) (o Bool)) (!
  (iff
    ($Set.in o ($Set.difference a b))
    (and
      ($Set.in o a)
      (not ($Set.in o b))))
  :pattern (($Set.in o ($Set.difference a b)))
  )))
(assert (forall ((a $Set<Bool>) (b $Set<Bool>) (y Bool)) (!
  (=>
    ($Set.in y b)
    (not ($Set.in y ($Set.difference a b))))
  :pattern (($Set.in y ($Set.difference a b)) ($Set.in y b))
  )))
(assert (forall ((a $Set<Bool>) (b $Set<Bool>)) (!
  (iff
    ($Set.subset a b)
    (forall ((o Bool)) (!
      (=>
        ($Set.in o a)
        ($Set.in o b))
      :pattern (($Set.in o a))
      :pattern (($Set.in o b))
    )))
  :pattern (($Set.subset a b))
  )))
(assert (forall ((a $Set<Bool>) (b $Set<Bool>)) (!
  (iff
    ($Set.equal a b)
    (forall ((o Bool)) (!
      (iff
        ($Set.in o a)
        ($Set.in o b))
      :pattern (($Set.in o a))
      :pattern (($Set.in o b))
      )))
  :pattern (($Set.equal a b))
  )))
(assert (forall ((a $Set<Bool>) (b $Set<Bool>)) (!
  (=>
    ($Set.equal a b)
    (= a b))
  :pattern (($Set.equal a b))
  )))
(assert (forall ((a $Set<Bool>) (b $Set<Bool>)) (!
  (iff
    ($Set.disjoint a b)
    (forall ((o Bool)) (!
      (or
        (not ($Set.in o a))
        (not ($Set.in o b)))
      :pattern (($Set.in o a))
      :pattern (($Set.in o b))
      )))
  :pattern (($Set.disjoint a b))
  )))
(assert (forall ((a $Set<Bool>) (b $Set<Bool>)) (!
  (and
    (=
      (+
        (+
          ($Set.card ($Set.difference a b))
          ($Set.card ($Set.difference b a)))
        ($Set.card ($Set.intersection a b)))
      ($Set.card ($Set.union a b)))
    (=
      ($Set.card ($Set.difference a b))
      (-
        ($Set.card a)
        ($Set.card ($Set.intersection a b)))))
  :pattern (($Set.card ($Set.difference a b)) ($Set.card ($Set.intersection a b)))
  )))
; /dafny_axioms/sets_axioms_dafny.smt2 [Ref]
(assert (forall ((s $Set<$Ref>)) (!
  (<= 0 ($Set.card s))
  :pattern (($Set.card s))
  )))
(assert (forall ((o $Ref)) (!
  (not ($Set.in o $Set.empty<$Ref>))
  :pattern (($Set.in o $Set.empty<$Ref>))
  )))
(assert (forall ((s $Set<$Ref>)) (!
  (and
    (iff
      (= ($Set.card s) 0)
      (= s $Set.empty<$Ref>))
    (implies
      (not (= ($Set.card s) 0))
      (exists ((x $Ref)) (!
        ($Set.in x s)
        :pattern (($Set.in x s))
      ))))
  :pattern (($Set.card s))
  )))
(assert (forall ((r $Ref)) (!
  ($Set.in r ($Set.singleton r))
  :pattern (($Set.in r ($Set.singleton r)))
  )))
(assert (forall ((r $Ref) (o $Ref)) (!
  (iff
    ($Set.in o ($Set.singleton r))
    (= r o))
  :pattern (($Set.in o ($Set.singleton r)))
  )))
(assert (forall ((r $Ref)) (!
  (= ($Set.card ($Set.singleton r)) 1)
  :pattern (($Set.card ($Set.singleton r)))
  )))
(assert (forall ((a $Set<$Ref>) (x $Ref) (o $Ref)) (!
  (iff
    ($Set.in o ($Set.unionone a x))
    (or
      (= o x)
      ($Set.in o a)))
  :pattern (($Set.in o ($Set.unionone a x)))
  )))
(assert (forall ((a $Set<$Ref>) (x $Ref)) (!
  ($Set.in x ($Set.unionone a x))
  :pattern (($Set.in x ($Set.unionone a x)))
  )))
(assert (forall ((a $Set<$Ref>) (x $Ref) (y $Ref)) (!
  (=>
    ($Set.in y a)
    ($Set.in y ($Set.unionone a x)))
  :pattern (($Set.in y a) ($Set.in y ($Set.unionone a x)))
  )))
(assert (forall ((a $Set<$Ref>) (x $Ref)) (!
  (=>
    ($Set.in x a)
    (= ($Set.card ($Set.unionone a x)) ($Set.card a)))
  :pattern (($Set.card ($Set.unionone a x)))
  )))
(assert (forall ((a $Set<$Ref>) (x $Ref)) (!
  (=>
    (not ($Set.in x a))
    (= ($Set.card ($Set.unionone a x)) (+ ($Set.card a) 1)))
  :pattern (($Set.card ($Set.unionone a x)))
  )))
(assert (forall ((a $Set<$Ref>) (b $Set<$Ref>) (o $Ref)) (!
  (iff
    ($Set.in o ($Set.union a b))
    (or
      ($Set.in o a)
      ($Set.in o b)))
  :pattern (($Set.in o ($Set.union a b)))
  )))
(assert (forall ((a $Set<$Ref>) (b $Set<$Ref>) (y $Ref)) (!
  (=>
    ($Set.in y a)
    ($Set.in y ($Set.union a b)))
  :pattern (($Set.in y ($Set.union a b)) ($Set.in y a))
  )))
(assert (forall ((a $Set<$Ref>) (b $Set<$Ref>) (y $Ref)) (!
  (=>
    ($Set.in y b)
    ($Set.in y ($Set.union a b)))
  :pattern (($Set.in y ($Set.union a b)) ($Set.in y b))
  )))
(assert (forall ((a $Set<$Ref>) (b $Set<$Ref>) (o $Ref)) (!
  (iff
    ($Set.in o ($Set.intersection a b))
    (and
      ($Set.in o a)
      ($Set.in o b)))
  :pattern (($Set.in o ($Set.intersection a b)))
  )))
(assert (forall ((a $Set<$Ref>) (b $Set<$Ref>)) (!
  (=
    ($Set.union ($Set.union a b) b)
    ($Set.union a b))
  :pattern (($Set.union ($Set.union a b) b))
  )))
(assert (forall ((a $Set<$Ref>) (b $Set<$Ref>)) (!
  (=
    ($Set.union a ($Set.union a b))
    ($Set.union a b))
    :pattern (($Set.union a ($Set.union a b)))
  )))
(assert (forall ((a $Set<$Ref>) (b $Set<$Ref>)) (!
  (=
    ($Set.intersection ($Set.intersection a b) b)
    ($Set.intersection a b))
  :pattern (($Set.intersection ($Set.intersection a b) b))
  )))
(assert (forall ((a $Set<$Ref>) (b $Set<$Ref>)) (!
  (=
    ($Set.intersection a ($Set.intersection a b))
    ($Set.intersection a b))
  :pattern (($Set.intersection a ($Set.intersection a b)))
  )))
(assert (forall ((a $Set<$Ref>) (b $Set<$Ref>)) (!
  (=
    (+
      ($Set.card ($Set.union a b))
      ($Set.card ($Set.intersection a b)))
    (+
      ($Set.card a)
      ($Set.card b)))
  :pattern (($Set.card ($Set.union a b)))
  :pattern (($Set.card ($Set.intersection a b)))
  )))
(assert (forall ((a $Set<$Ref>) (b $Set<$Ref>) (o $Ref)) (!
  (iff
    ($Set.in o ($Set.difference a b))
    (and
      ($Set.in o a)
      (not ($Set.in o b))))
  :pattern (($Set.in o ($Set.difference a b)))
  )))
(assert (forall ((a $Set<$Ref>) (b $Set<$Ref>) (y $Ref)) (!
  (=>
    ($Set.in y b)
    (not ($Set.in y ($Set.difference a b))))
  :pattern (($Set.in y ($Set.difference a b)) ($Set.in y b))
  )))
(assert (forall ((a $Set<$Ref>) (b $Set<$Ref>)) (!
  (iff
    ($Set.subset a b)
    (forall ((o $Ref)) (!
      (=>
        ($Set.in o a)
        ($Set.in o b))
      :pattern (($Set.in o a))
      :pattern (($Set.in o b))
    )))
  :pattern (($Set.subset a b))
  )))
(assert (forall ((a $Set<$Ref>) (b $Set<$Ref>)) (!
  (iff
    ($Set.equal a b)
    (forall ((o $Ref)) (!
      (iff
        ($Set.in o a)
        ($Set.in o b))
      :pattern (($Set.in o a))
      :pattern (($Set.in o b))
      )))
  :pattern (($Set.equal a b))
  )))
(assert (forall ((a $Set<$Ref>) (b $Set<$Ref>)) (!
  (=>
    ($Set.equal a b)
    (= a b))
  :pattern (($Set.equal a b))
  )))
(assert (forall ((a $Set<$Ref>) (b $Set<$Ref>)) (!
  (iff
    ($Set.disjoint a b)
    (forall ((o $Ref)) (!
      (or
        (not ($Set.in o a))
        (not ($Set.in o b)))
      :pattern (($Set.in o a))
      :pattern (($Set.in o b))
      )))
  :pattern (($Set.disjoint a b))
  )))
(assert (forall ((a $Set<$Ref>) (b $Set<$Ref>)) (!
  (and
    (=
      (+
        (+
          ($Set.card ($Set.difference a b))
          ($Set.card ($Set.difference b a)))
        ($Set.card ($Set.intersection a b)))
      ($Set.card ($Set.union a b)))
    (=
      ($Set.card ($Set.difference a b))
      (-
        ($Set.card a)
        ($Set.card ($Set.intersection a b)))))
  :pattern (($Set.card ($Set.difference a b)) ($Set.card ($Set.intersection a b)))
  )))
; Declaring additional sort wrappers
(declare-fun $SortWrappers.$PermTo$Snap ($Perm) $Snap)
(declare-fun $SortWrappers.$SnapTo$Perm ($Snap) $Perm)
(assert (forall ((x $Perm)) (!
    (= x ($SortWrappers.$SnapTo$Perm($SortWrappers.$PermTo$Snap x)))
    :pattern (($SortWrappers.$PermTo$Snap x))
    )))
(declare-fun $SortWrappers.$RefTo$Snap ($Ref) $Snap)
(declare-fun $SortWrappers.$SnapTo$Ref ($Snap) $Ref)
(assert (forall ((x $Ref)) (!
    (= x ($SortWrappers.$SnapTo$Ref($SortWrappers.$RefTo$Snap x)))
    :pattern (($SortWrappers.$RefTo$Snap x))
    )))
(declare-fun $SortWrappers.BoolTo$Snap (Bool) $Snap)
(declare-fun $SortWrappers.$SnapToBool ($Snap) Bool)
(assert (forall ((x Bool)) (!
    (= x ($SortWrappers.$SnapToBool($SortWrappers.BoolTo$Snap x)))
    :pattern (($SortWrappers.BoolTo$Snap x))
    )))
(declare-fun $SortWrappers.IntTo$Snap (Int) $Snap)
(declare-fun $SortWrappers.$SnapToInt ($Snap) Int)
(assert (forall ((x Int)) (!
    (= x ($SortWrappers.$SnapToInt($SortWrappers.IntTo$Snap x)))
    :pattern (($SortWrappers.IntTo$Snap x))
    )))
; Declaring additional sort wrappers
(declare-fun $SortWrappers.$Seq<$Ref>To$Snap ($Seq<$Ref>) $Snap)
(declare-fun $SortWrappers.$SnapTo$Seq<$Ref> ($Snap) $Seq<$Ref>)
(assert (forall ((x $Seq<$Ref>)) (!
    (= x ($SortWrappers.$SnapTo$Seq<$Ref>($SortWrappers.$Seq<$Ref>To$Snap x)))
    :pattern (($SortWrappers.$Seq<$Ref>To$Snap x))
    )))
; Declaring additional sort wrappers
(declare-fun $SortWrappers.$Set<$Ref>To$Snap ($Set<$Ref>) $Snap)
(declare-fun $SortWrappers.$SnapTo$Set<$Ref> ($Snap) $Set<$Ref>)
(assert (forall ((x $Set<$Ref>)) (!
    (= x ($SortWrappers.$SnapTo$Set<$Ref>($SortWrappers.$Set<$Ref>To$Snap x)))
    :pattern (($SortWrappers.$Set<$Ref>To$Snap x))
    )))
(declare-fun $SortWrappers.$Set<Bool>To$Snap ($Set<Bool>) $Snap)
(declare-fun $SortWrappers.$SnapTo$Set<Bool> ($Snap) $Set<Bool>)
(assert (forall ((x $Set<Bool>)) (!
    (= x ($SortWrappers.$SnapTo$Set<Bool>($SortWrappers.$Set<Bool>To$Snap x)))
    :pattern (($SortWrappers.$Set<Bool>To$Snap x))
    )))
(declare-fun $SortWrappers.$Set<$Seq<$Ref>>To$Snap ($Set<$Seq<$Ref>>) $Snap)
(declare-fun $SortWrappers.$SnapTo$Set<$Seq<$Ref>> ($Snap) $Set<$Seq<$Ref>>)
(assert (forall ((x $Set<$Seq<$Ref>>)) (!
    (= x ($SortWrappers.$SnapTo$Set<$Seq<$Ref>>($SortWrappers.$Set<$Seq<$Ref>>To$Snap x)))
    :pattern (($SortWrappers.$Set<$Seq<$Ref>>To$Snap x))
    )))
(declare-fun $SortWrappers.$Set<Int>To$Snap ($Set<Int>) $Snap)
(declare-fun $SortWrappers.$SnapTo$Set<Int> ($Snap) $Set<Int>)
(assert (forall ((x $Set<Int>)) (!
    (= x ($SortWrappers.$SnapTo$Set<Int>($SortWrappers.$Set<Int>To$Snap x)))
    :pattern (($SortWrappers.$Set<Int>To$Snap x))
    )))
; Declaring additional sort wrappers
(declare-fun $SortWrappers.$FVF<Int>To$Snap ($FVF<Int>) $Snap)
(declare-fun $SortWrappers.$SnapTo$FVF<Int> ($Snap) $FVF<Int>)
(assert (forall ((x $FVF<Int>)) (!
    (= x ($SortWrappers.$SnapTo$FVF<Int>($SortWrappers.$FVF<Int>To$Snap x)))
    :pattern (($SortWrappers.$FVF<Int>To$Snap x))
    )))
(declare-fun $SortWrappers.$FVF<Bool>To$Snap ($FVF<Bool>) $Snap)
(declare-fun $SortWrappers.$SnapTo$FVF<Bool> ($Snap) $FVF<Bool>)
(assert (forall ((x $FVF<Bool>)) (!
    (= x ($SortWrappers.$SnapTo$FVF<Bool>($SortWrappers.$FVF<Bool>To$Snap x)))
    :pattern (($SortWrappers.$FVF<Bool>To$Snap x))
    )))
(declare-fun $SortWrappers.$FVF<$Seq<$Ref>>To$Snap ($FVF<$Seq<$Ref>>) $Snap)
(declare-fun $SortWrappers.$SnapTo$FVF<$Seq<$Ref>> ($Snap) $FVF<$Seq<$Ref>>)
(assert (forall ((x $FVF<$Seq<$Ref>>)) (!
    (= x ($SortWrappers.$SnapTo$FVF<$Seq<$Ref>>($SortWrappers.$FVF<$Seq<$Ref>>To$Snap x)))
    :pattern (($SortWrappers.$FVF<$Seq<$Ref>>To$Snap x))
    )))
(declare-fun $SortWrappers.$FVF<$Ref>To$Snap ($FVF<$Ref>) $Snap)
(declare-fun $SortWrappers.$SnapTo$FVF<$Ref> ($Snap) $FVF<$Ref>)
(assert (forall ((x $FVF<$Ref>)) (!
    (= x ($SortWrappers.$SnapTo$FVF<$Ref>($SortWrappers.$FVF<$Ref>To$Snap x)))
    :pattern (($SortWrappers.$FVF<$Ref>To$Snap x))
    )))
; /field_value_functions_axioms.smt2 [Set__contents: Seq[Ref]]
(assert (forall ((vs $FVF<$Seq<$Ref>>) (ws $FVF<$Seq<$Ref>>)) (!
    (implies
      (and
        ($Set.equal ($FVF.domain_Set__contents vs) ($FVF.domain_Set__contents ws))
        (forall ((x $Ref)) (!
          (implies
            ($Set.in x ($FVF.domain_Set__contents vs))
            (= ($FVF.lookup_Set__contents vs x) ($FVF.lookup_Set__contents ws x)))
          :pattern (($FVF.lookup_Set__contents vs x) ($FVF.lookup_Set__contents ws x)))))
      (= vs ws))
    :pattern (($SortWrappers.$FVF<$Seq<$Ref>>To$Snap vs)
              ($SortWrappers.$FVF<$Seq<$Ref>>To$Snap ws))
    )))
; /field_value_functions_axioms.smt2 [Ref__Boolean_value: Bool]
(assert (forall ((vs $FVF<Bool>) (ws $FVF<Bool>)) (!
    (implies
      (and
        ($Set.equal ($FVF.domain_Ref__Boolean_value vs) ($FVF.domain_Ref__Boolean_value ws))
        (forall ((x $Ref)) (!
          (implies
            ($Set.in x ($FVF.domain_Ref__Boolean_value vs))
            (= ($FVF.lookup_Ref__Boolean_value vs x) ($FVF.lookup_Ref__Boolean_value ws x)))
          :pattern (($FVF.lookup_Ref__Boolean_value vs x) ($FVF.lookup_Ref__Boolean_value ws x)))))
      (= vs ws))
    :pattern (($SortWrappers.$FVF<Bool>To$Snap vs)
              ($SortWrappers.$FVF<Bool>To$Snap ws))
    )))
; /field_value_functions_axioms.smt2 [Set__max: Int]
(assert (forall ((vs $FVF<Int>) (ws $FVF<Int>)) (!
    (implies
      (and
        ($Set.equal ($FVF.domain_Set__max vs) ($FVF.domain_Set__max ws))
        (forall ((x $Ref)) (!
          (implies
            ($Set.in x ($FVF.domain_Set__max vs))
            (= ($FVF.lookup_Set__max vs x) ($FVF.lookup_Set__max ws x)))
          :pattern (($FVF.lookup_Set__max vs x) ($FVF.lookup_Set__max ws x)))))
      (= vs ws))
    :pattern (($SortWrappers.$FVF<Int>To$Snap vs)
              ($SortWrappers.$FVF<Int>To$Snap ws))
    )))
; Preamble end
; ------------------------------------------------------------
; ------------------------------------------------------------
; Declaring program functions
(declare-const s@$ $Snap)
; ---------- Set__Set ----------
(declare-const max@1 Int)
(declare-const sys__result@2 $Ref)
(declare-const diz@3 $Ref)
(declare-const __flatten_1@4 Int)
(declare-const __flatten_2@5 $Seq<$Ref>)
(declare-const i@6 Int)
(declare-const __flatten_3@7 Int)
(declare-const __flatten_5@8 $Seq<$Ref>)
(declare-const __flatten_6@9 $Ref)
(declare-const __flatten_7@10 Bool)
(push) ; 2
; [eval] max > 0
(assert (> max@1 0))
(push) ; 3
; [eval] sys__result != null
(assert (not (= sys__result@2 $Ref.null)))
(declare-const $k@11 $Perm)
(assert ($Perm.isValidVar $k@11))
(assert ($Perm.isReadVar $k@11 $Perm.Write))
(declare-const $t@12 Int)
; [eval] sys__result.Set__max > 0
(set-option :timeout 0)
(push) ; 4
(assert (not (not (= $k@11 $Perm.No))))
(check-sat)
; unsat
(pop) ; 4
; 0.00s
; (get-info :all-statistics)
(assert (not (= $k@11 $Perm.No)))
(assert (> $t@12 0))
(declare-const $k@13 $Perm)
(assert ($Perm.isValidVar $k@13))
(assert ($Perm.isReadVar $k@13 $Perm.Write))
(declare-const $t@14 $Seq<$Ref>)
; [eval] |sys__result.Set__contents| == sys__result.Set__max
; [eval] |sys__result.Set__contents|
(set-option :timeout 0)
(push) ; 4
(assert (not (not (= $k@13 $Perm.No))))
(check-sat)
; unsat
(pop) ; 4
; 0.00s
; (get-info :all-statistics)
(assert (not (= $k@13 $Perm.No)))
(assert (= ($Seq.length $t@14) $t@12))
(declare-const k@15 Int)
(push) ; 4
; [eval] (0 <= k) && (k < sys__result.Set__max)
; [eval] 0 <= k
(push) ; 5
(set-option :timeout 0)
(push) ; 6
(assert (not (not (<= 0 k@15))))
(check-sat)
; unknown
(pop) ; 6
; 0.00s
; (get-info :all-statistics)
(set-option :timeout 0)
(push) ; 6
(assert (not (<= 0 k@15)))
(check-sat)
; unknown
(pop) ; 6
; 0.00s
; (get-info :all-statistics)
(push) ; 6
; [then-branch 1] 0 <= k@15
(assert (<= 0 k@15))
; [eval] k < sys__result.Set__max
(pop) ; 6
(push) ; 6
; [else-branch 1] !0 <= k@15
(assert (not (<= 0 k@15)))
(pop) ; 6
(pop) ; 5
(assert (and (<= 0 k@15) (< k@15 $t@12)))
; [eval] sys__result.Set__contents[k]
(pop) ; 4
(declare-const $t@16 $FVF<Bool>)
(declare-fun invOf@17 ($Ref) Int)
(assert (forall (($r $Ref)) (!
  (implies
    (and (<= 0 (invOf@17 $r)) (< (invOf@17 $r) $t@12))
    (= ($Seq.index $t@14 (invOf@17 $r)) $r))
  :pattern ((invOf@17 $r)))))
(assert (forall ((k@15 Int)) (!
  (implies
    (and (<= 0 k@15) (< k@15 $t@12))
    (= (invOf@17 ($Seq.index $t@14 k@15)) k@15))
  :pattern (($Seq.index $t@14 k@15)))))
(assert (forall ((k@15 Int)) (!
  (iff
    ($Set.in ($Seq.index $t@14 k@15) ($FVF.domain_Ref__Boolean_value $t@16))
    (and (<= 0 k@15) (< k@15 $t@12)))
  :pattern (($Set.in
    ($Seq.index $t@14 k@15)
    ($FVF.domain_Ref__Boolean_value $t@16))))))
(assert (forall ((k@15 Int)) (!
  (implies
    (and (<= 0 k@15) (< k@15 $t@12))
    (not (= ($Seq.index $t@14 k@15) $Ref.null)))
  :pattern (($Seq.index $t@14 k@15)))))
; [eval] sys__result.Set__max == max
(assert (= $t@12 max@1))
; [eval] (forall k: Int :: (0 <= k) && (k < max) ==> !sys__result.Set__contents[k].Ref__Boolean_value)
(declare-const k@18 Int)
(push) ; 4
; [eval] (0 <= k) && (k < max) ==> !sys__result.Set__contents[k].Ref__Boolean_value
; [eval] (0 <= k) && (k < max)
; [eval] 0 <= k
(push) ; 5
(set-option :timeout 0)
(push) ; 6
(assert (not (not (<= 0 k@18))))
(check-sat)
; unknown
(pop) ; 6
; 0.00s
; (get-info :all-statistics)
(set-option :timeout 0)
(push) ; 6
(assert (not (<= 0 k@18)))
(check-sat)
; unknown
(pop) ; 6
; 0.00s
; (get-info :all-statistics)
(push) ; 6
; [then-branch 2] 0 <= k@18
(assert (<= 0 k@18))
; [eval] k < max
(pop) ; 6
(push) ; 6
; [else-branch 2] !0 <= k@18
(assert (not (<= 0 k@18)))
(pop) ; 6
(pop) ; 5
(push) ; 5
(set-option :timeout 0)
(push) ; 6
(assert (not (not (and (<= 0 k@18) (< k@18 max@1)))))
(check-sat)
; unknown
(pop) ; 6
; 0.00s
; (get-info :all-statistics)
(set-option :timeout 0)
(push) ; 6
(assert (not (and (<= 0 k@18) (< k@18 max@1))))
(check-sat)
; unknown
(pop) ; 6
; 0.00s
; (get-info :all-statistics)
(push) ; 6
; [then-branch 3] 0 <= k@18 && k@18 < max@1
(assert (and (<= 0 k@18) (< k@18 max@1)))
; [eval] !sys__result.Set__contents[k].Ref__Boolean_value
; [eval] sys__result.Set__contents[k]
(set-option :timeout 0)
(push) ; 7
(assert (not (not (= ($Seq.index $t@14 k@18) $Ref.null))))
(check-sat)
; unsat
(pop) ; 7
; 0.00s
; (get-info :all-statistics)
(set-option :timeout 0)
(push) ; 7
(assert (not (and
  (<= 0 (invOf@17 ($Seq.index $t@14 k@18)))
  (< (invOf@17 ($Seq.index $t@14 k@18)) $t@12))))
(check-sat)
; unsat
(pop) ; 7
; 0.00s
; (get-info :all-statistics)
(declare-const fvf@19 $FVF<Bool>)
(assert (forall (($r $Ref)) (!
  (implies
    (and
      (and (<= 0 (invOf@17 $r)) (< (invOf@17 $r) $t@12))
      ($Set.in $r ($FVF.domain_Ref__Boolean_value fvf@19)))
    (=
      ($FVF.lookup_Ref__Boolean_value fvf@19 $r)
      ($FVF.lookup_Ref__Boolean_value $t@16 $r)))
  :pattern (($FVF.lookup_Ref__Boolean_value fvf@19 $r) (invOf@17 $r))
  :pattern (($FVF.lookup_Ref__Boolean_value $t@16 $r) (invOf@17 $r)))))
(assert (forall ((k@18 Int)) (!
  (iff
    ($Set.in ($Seq.index $t@14 k@18) ($FVF.domain_Ref__Boolean_value fvf@19))
    (and (<= 0 k@18) (< k@18 max@1)))
  :pattern (($Set.in
    ($Seq.index $t@14 k@18)
    ($FVF.domain_Ref__Boolean_value fvf@19))))))
(pop) ; 6
(push) ; 6
; [else-branch 3] !0 <= k@18 && k@18 < max@1
(assert (not (and (<= 0 k@18) (< k@18 max@1))))
(pop) ; 6
(pop) ; 5
(assert (forall ((k@18 Int)) (!
  (iff
    ($Set.in ($Seq.index $t@14 k@18) ($FVF.domain_Ref__Boolean_value fvf@19))
    (and (<= 0 k@18) (< k@18 max@1)))
  :pattern (($Set.in
    ($Seq.index $t@14 k@18)
    ($FVF.domain_Ref__Boolean_value fvf@19))))))
(assert (forall (($r $Ref)) (!
  (implies
    (and
      (and (<= 0 (invOf@17 $r)) (< (invOf@17 $r) $t@12))
      ($Set.in $r ($FVF.domain_Ref__Boolean_value fvf@19)))
    (=
      ($FVF.lookup_Ref__Boolean_value fvf@19 $r)
      ($FVF.lookup_Ref__Boolean_value $t@16 $r)))
  :pattern (($FVF.lookup_Ref__Boolean_value fvf@19 $r) (invOf@17 $r))
  :pattern (($FVF.lookup_Ref__Boolean_value $t@16 $r) (invOf@17 $r)))))
(pop) ; 4
(assert (forall ((k@18 Int)) (!
  (iff
    ($Set.in ($Seq.index $t@14 k@18) ($FVF.domain_Ref__Boolean_value fvf@19))
    (and (<= 0 k@18) (< k@18 max@1)))
  :pattern (($Set.in
    ($Seq.index $t@14 k@18)
    ($FVF.domain_Ref__Boolean_value fvf@19))))))
(assert (forall (($r $Ref)) (!
  (implies
    (and
      (and (<= 0 (invOf@17 $r)) (< (invOf@17 $r) $t@12))
      ($Set.in $r ($FVF.domain_Ref__Boolean_value fvf@19)))
    (=
      ($FVF.lookup_Ref__Boolean_value fvf@19 $r)
      ($FVF.lookup_Ref__Boolean_value $t@16 $r)))
  :pattern (($FVF.lookup_Ref__Boolean_value fvf@19 $r) (invOf@17 $r))
  :pattern (($FVF.lookup_Ref__Boolean_value $t@16 $r) (invOf@17 $r)))))
(assert (forall ((k@18 Int)) (!
  (implies
    (and (<= 0 k@18) (< k@18 max@1))
    (not ($FVF.lookup_Ref__Boolean_value fvf@19 ($Seq.index $t@14 k@18))))
  :pattern (($Seq.index $t@14 k@18)))))
(pop) ; 3
(push) ; 3
; [exec]
; diz := new(Set__max, Set__contents, Set__Integer_value, Set__Boolean_value)
(declare-const diz@20 $Ref)
(assert (not (= diz@20 $Ref.null)))
(declare-const Set__max@21 Int)
(declare-const Set__contents@22 $Seq<$Ref>)
(declare-const Set__Integer_value@23 Int)
(declare-const Set__Boolean_value@24 Bool)
(assert (and (not (= sys__result@2 diz@20)) (not (= __flatten_6@9 diz@20))))
; [exec]
; __flatten_1 := max
; [exec]
; __flatten_3 := __flatten_1
; [exec]
; diz.Set__max := __flatten_3
; [exec]
; __flatten_2 := Set__new_array_Boolean(diz, max)
; [eval] diz != null
(declare-const sys__result@25 $Seq<$Ref>)
(declare-const $t@26 $Snap)
(declare-const $t@27 $FVF<Bool>)
(assert (= $t@26 ($Snap.combine $Snap.unit ($SortWrappers.$FVF<Bool>To$Snap $t@27))))
; [eval] |sys__result| == len
; [eval] |sys__result|
(assert (= ($Seq.length sys__result@25) max@1))
(declare-const i@28 Int)
(push) ; 4
; [eval] (0 <= i) && (i < |sys__result|)
; [eval] 0 <= i
(push) ; 5
(set-option :timeout 0)
(push) ; 6
(assert (not (not (<= 0 i@28))))
(check-sat)
; unknown
(pop) ; 6
; 0.00s
; (get-info :all-statistics)
(set-option :timeout 0)
(push) ; 6
(assert (not (<= 0 i@28)))
(check-sat)
; unknown
(pop) ; 6
; 0.00s
; (get-info :all-statistics)
(push) ; 6
; [then-branch 4] 0 <= i@28
(assert (<= 0 i@28))
; [eval] i < |sys__result|
; [eval] |sys__result|
(pop) ; 6
(push) ; 6
; [else-branch 4] !0 <= i@28
(assert (not (<= 0 i@28)))
(pop) ; 6
(pop) ; 5
(assert (and (<= 0 i@28) (< i@28 ($Seq.length sys__result@25))))
; [eval] sys__result[i]
(pop) ; 4
(declare-fun invOf@29 ($Ref) Int)
(assert (forall (($r $Ref)) (!
  (implies
    (and (<= 0 (invOf@29 $r)) (< (invOf@29 $r) ($Seq.length sys__result@25)))
    (= ($Seq.index sys__result@25 (invOf@29 $r)) $r))
  :pattern ((invOf@29 $r)))))
(assert (forall ((i@28 Int)) (!
  (implies
    (and (<= 0 i@28) (< i@28 ($Seq.length sys__result@25)))
    (= (invOf@29 ($Seq.index sys__result@25 i@28)) i@28))
  :pattern (($Seq.index sys__result@25 i@28)))))
(assert (forall ((i@28 Int)) (!
  (iff
    ($Set.in
      ($Seq.index sys__result@25 i@28)
      ($FVF.domain_Ref__Boolean_value $t@27))
    (and (<= 0 i@28) (< i@28 ($Seq.length sys__result@25))))
  :pattern (($Set.in
    ($Seq.index sys__result@25 i@28)
    ($FVF.domain_Ref__Boolean_value $t@27))))))
(assert (forall ((i@28 Int)) (!
  (implies
    (and (<= 0 i@28) (< i@28 ($Seq.length sys__result@25)))
    (not (= ($Seq.index sys__result@25 i@28) $Ref.null)))
  :pattern (($Seq.index sys__result@25 i@28)))))
; [exec]
; __flatten_5 := __flatten_2
; [exec]
; diz.Set__contents := __flatten_5
; [exec]
; i := 0
; loop at <no position>
(declare-const i@30 Int)
(declare-const __flatten_7@31 Bool)
(declare-const __flatten_6@32 $Ref)
(push) ; 4
; Verify loop body
(declare-const $t@33 $Snap)
(declare-const $t@34 $Snap)
(assert (= $t@33 ($Snap.combine $t@34 $Snap.unit)))
(declare-const $t@35 $Snap)
(assert (= $t@34 ($Snap.combine $t@35 $Snap.unit)))
(declare-const $t@36 $Snap)
(assert (= $t@35 ($Snap.combine $t@36 $Snap.unit)))
(declare-const $t@37 $Snap)
(declare-const $t@38 $FVF<Bool>)
(assert (= $t@36 ($Snap.combine $t@37 ($SortWrappers.$FVF<Bool>To$Snap $t@38))))
(declare-const $t@39 $Snap)
(assert (= $t@37 ($Snap.combine $t@39 $Snap.unit)))
(declare-const $t@40 Int)
(declare-const $t@41 $Seq<$Ref>)
(assert (=
  $t@39
  ($Snap.combine
    ($SortWrappers.IntTo$Snap $t@40)
    ($SortWrappers.$Seq<$Ref>To$Snap $t@41))))
(declare-const $t@42 Int)
(assert (=
  ($SortWrappers.IntTo$Snap $t@40)
  ($Snap.combine ($SortWrappers.IntTo$Snap $t@42) $Snap.unit)))
(declare-const $t@43 Int)
(assert (=
  ($SortWrappers.IntTo$Snap $t@42)
  ($Snap.combine $Snap.unit ($SortWrappers.IntTo$Snap $t@43))))
; [eval] (0 <= i) && (i <= max)
; [eval] 0 <= i
(push) ; 5
(set-option :timeout 0)
(push) ; 6
(assert (not (not (<= 0 i@30))))
(check-sat)
; unknown
(pop) ; 6
; 0.00s
; (get-info :all-statistics)
(set-option :timeout 0)
(push) ; 6
(assert (not (<= 0 i@30)))
(check-sat)
; unknown
(pop) ; 6
; 0.00s
; (get-info :all-statistics)
(push) ; 6
; [then-branch 5] 0 <= i@30
(assert (<= 0 i@30))
; [eval] i <= max
(pop) ; 6
(push) ; 6
; [else-branch 5] !0 <= i@30
(assert (not (<= 0 i@30)))
(pop) ; 6
(pop) ; 5
(assert (and (<= 0 i@30) (<= i@30 max@1)))
(declare-const $k@44 $Perm)
(assert ($Perm.isValidVar $k@44))
(assert ($Perm.isReadVar $k@44 $Perm.Write))
; [eval] diz.Set__max > 0
(set-option :timeout 0)
(push) ; 5
(assert (not (not (= $k@44 $Perm.No))))
(check-sat)
; unsat
(pop) ; 5
; 0.00s
; (get-info :all-statistics)
(assert (not (= $k@44 $Perm.No)))
(assert (> $t@43 0))
(declare-const $k@45 $Perm)
(assert ($Perm.isValidVar $k@45))
(assert ($Perm.isReadVar $k@45 $Perm.Write))
; [eval] |diz.Set__contents| == diz.Set__max
; [eval] |diz.Set__contents|
(set-option :timeout 0)
(push) ; 5
(assert (not (not (= $k@45 $Perm.No))))
(check-sat)
; unsat
(pop) ; 5
; 0.00s
; (get-info :all-statistics)
(assert (not (= $k@45 $Perm.No)))
(assert (= ($Seq.length $t@41) $t@43))
(declare-const k@46 Int)
(push) ; 5
; [eval] (0 <= k) && (k < diz.Set__max)
; [eval] 0 <= k
(push) ; 6
(set-option :timeout 0)
(push) ; 7
(assert (not (not (<= 0 k@46))))
(check-sat)
; unknown
(pop) ; 7
; 0.00s
; (get-info :all-statistics)
(set-option :timeout 0)
(push) ; 7
(assert (not (<= 0 k@46)))
(check-sat)
; unknown
(pop) ; 7
; 0.00s
; (get-info :all-statistics)
(push) ; 7
; [then-branch 6] 0 <= k@46
(assert (<= 0 k@46))
; [eval] k < diz.Set__max
(pop) ; 7
(push) ; 7
; [else-branch 6] !0 <= k@46
(assert (not (<= 0 k@46)))
(pop) ; 7
(pop) ; 6
(assert (and (<= 0 k@46) (< k@46 $t@43)))
; [eval] diz.Set__contents[k]
(pop) ; 5
(declare-fun invOf@47 ($Ref) Int)
(assert (forall (($r $Ref)) (!
  (implies
    (and (<= 0 (invOf@47 $r)) (< (invOf@47 $r) $t@43))
    (= ($Seq.index $t@41 (invOf@47 $r)) $r))
  :pattern ((invOf@47 $r)))))
(assert (forall ((k@46 Int)) (!
  (implies
    (and (<= 0 k@46) (< k@46 $t@43))
    (= (invOf@47 ($Seq.index $t@41 k@46)) k@46))
  :pattern (($Seq.index $t@41 k@46)))))
(assert (forall ((k@46 Int)) (!
  (iff
    ($Set.in ($Seq.index $t@41 k@46) ($FVF.domain_Ref__Boolean_value $t@38))
    (and (<= 0 k@46) (< k@46 $t@43)))
  :pattern (($Set.in
    ($Seq.index $t@41 k@46)
    ($FVF.domain_Ref__Boolean_value $t@38))))))
(assert (forall ((k@46 Int)) (!
  (implies
    (and (<= 0 k@46) (< k@46 $t@43))
    (not (= ($Seq.index $t@41 k@46) $Ref.null)))
  :pattern (($Seq.index $t@41 k@46)))))
; [eval] diz.Set__max == max
(assert (= $t@43 max@1))
; [eval] (forall k: Int :: (0 <= k) && (k < i) ==> !diz.Set__contents[k].Ref__Boolean_value)
(declare-const k@48 Int)
(push) ; 5
; [eval] (0 <= k) && (k < i) ==> !diz.Set__contents[k].Ref__Boolean_value
; [eval] (0 <= k) && (k < i)
; [eval] 0 <= k
(push) ; 6
(set-option :timeout 0)
(push) ; 7
(assert (not (not (<= 0 k@48))))
(check-sat)
; unknown
(pop) ; 7
; 0.00s
; (get-info :all-statistics)
(set-option :timeout 0)
(push) ; 7
(assert (not (<= 0 k@48)))
(check-sat)
; unknown
(pop) ; 7
; 0.00s
; (get-info :all-statistics)
(push) ; 7
; [then-branch 7] 0 <= k@48
(assert (<= 0 k@48))
; [eval] k < i
(pop) ; 7
(push) ; 7
; [else-branch 7] !0 <= k@48
(assert (not (<= 0 k@48)))
(pop) ; 7
(pop) ; 6
(push) ; 6
(set-option :timeout 0)
(push) ; 7
(assert (not (not (and (<= 0 k@48) (< k@48 i@30)))))
(check-sat)
; unknown
(pop) ; 7
; 0.00s
; (get-info :all-statistics)
(set-option :timeout 0)
(push) ; 7
(assert (not (and (<= 0 k@48) (< k@48 i@30))))
(check-sat)
; unknown
(pop) ; 7
; 0.00s
; (get-info :all-statistics)
(push) ; 7
; [then-branch 8] 0 <= k@48 && k@48 < i@30
(assert (and (<= 0 k@48) (< k@48 i@30)))
; [eval] !diz.Set__contents[k].Ref__Boolean_value
; [eval] diz.Set__contents[k]
(set-option :timeout 0)
(push) ; 8
(assert (not (not (= ($Seq.index $t@41 k@48) $Ref.null))))
(check-sat)
; unsat
(pop) ; 8
; 0.00s
; (get-info :all-statistics)
(set-option :timeout 0)
(push) ; 8
(assert (not (and
  (<= 0 (invOf@47 ($Seq.index $t@41 k@48)))
  (< (invOf@47 ($Seq.index $t@41 k@48)) $t@43))))
(check-sat)
; unsat
(pop) ; 8
; 0.00s
; (get-info :all-statistics)
(declare-const fvf@49 $FVF<Bool>)
(assert (forall (($r $Ref)) (!
  (implies
    (and
      (and (<= 0 (invOf@47 $r)) (< (invOf@47 $r) $t@43))
      ($Set.in $r ($FVF.domain_Ref__Boolean_value fvf@49)))
    (=
      ($FVF.lookup_Ref__Boolean_value fvf@49 $r)
      ($FVF.lookup_Ref__Boolean_value $t@38 $r)))
  :pattern (($FVF.lookup_Ref__Boolean_value fvf@49 $r) (invOf@47 $r))
  :pattern (($FVF.lookup_Ref__Boolean_value $t@38 $r) (invOf@47 $r)))))
(assert (forall ((k@48 Int)) (!
  (iff
    ($Set.in ($Seq.index $t@41 k@48) ($FVF.domain_Ref__Boolean_value fvf@49))
    (and (<= 0 k@48) (< k@48 i@30)))
  :pattern (($Set.in
    ($Seq.index $t@41 k@48)
    ($FVF.domain_Ref__Boolean_value fvf@49))))))
(pop) ; 7
(push) ; 7
; [else-branch 8] !0 <= k@48 && k@48 < i@30
(assert (not (and (<= 0 k@48) (< k@48 i@30))))
(pop) ; 7
(pop) ; 6
(assert (forall ((k@48 Int)) (!
  (iff
    ($Set.in ($Seq.index $t@41 k@48) ($FVF.domain_Ref__Boolean_value fvf@49))
    (and (<= 0 k@48) (< k@48 i@30)))
  :pattern (($Set.in
    ($Seq.index $t@41 k@48)
    ($FVF.domain_Ref__Boolean_value fvf@49))))))
(assert (forall (($r $Ref)) (!
  (implies
    (and
      (and (<= 0 (invOf@47 $r)) (< (invOf@47 $r) $t@43))
      ($Set.in $r ($FVF.domain_Ref__Boolean_value fvf@49)))
    (=
      ($FVF.lookup_Ref__Boolean_value fvf@49 $r)
      ($FVF.lookup_Ref__Boolean_value $t@38 $r)))
  :pattern (($FVF.lookup_Ref__Boolean_value fvf@49 $r) (invOf@47 $r))
  :pattern (($FVF.lookup_Ref__Boolean_value $t@38 $r) (invOf@47 $r)))))
(pop) ; 5
(assert (forall ((k@48 Int)) (!
  (iff
    ($Set.in ($Seq.index $t@41 k@48) ($FVF.domain_Ref__Boolean_value fvf@49))
    (and (<= 0 k@48) (< k@48 i@30)))
  :pattern (($Set.in
    ($Seq.index $t@41 k@48)
    ($FVF.domain_Ref__Boolean_value fvf@49))))))
(assert (forall (($r $Ref)) (!
  (implies
    (and
      (and (<= 0 (invOf@47 $r)) (< (invOf@47 $r) $t@43))
      ($Set.in $r ($FVF.domain_Ref__Boolean_value fvf@49)))
    (=
      ($FVF.lookup_Ref__Boolean_value fvf@49 $r)
      ($FVF.lookup_Ref__Boolean_value $t@38 $r)))
  :pattern (($FVF.lookup_Ref__Boolean_value fvf@49 $r) (invOf@47 $r))
  :pattern (($FVF.lookup_Ref__Boolean_value $t@38 $r) (invOf@47 $r)))))
(assert (forall ((k@48 Int)) (!
  (implies
    (and (<= 0 k@48) (< k@48 i@30))
    (not ($FVF.lookup_Ref__Boolean_value fvf@49 ($Seq.index $t@41 k@48))))
  :pattern (($Seq.index $t@41 k@48)))))
; [eval] i < max
(assert (< i@30 max@1))
(set-option :timeout 0)
(check-sat)
; unknown
; [exec]
; __flatten_6 := diz.Set__contents[i]
; [eval] diz.Set__contents[i]
; [exec]
; __flatten_7 := false
; [exec]
; __flatten_6.Ref__Boolean_value := __flatten_7
(set-option :timeout 0)
(push) ; 5
(assert (not (not (= ($Seq.index $t@41 i@30) $Ref.null))))
(check-sat)
; unsat
(pop) ; 5
; 0.00s
; (get-info :all-statistics)
(declare-const fvf@50 $FVF<Bool>)
; Precomputing split data for $t@41[i@30].Ref__Boolean_value # W
(define-fun $permsTaken1 (($r $Ref)) $Perm
  ($Perm.min
    (ite (= $r ($Seq.index $t@41 i@30)) $Perm.Write $Perm.No)
    (ite
      (= $r ($Seq.index $t@41 i@30))
      (ite
        (and (<= 0 (invOf@47 $r)) (< (invOf@47 $r) $t@43))
        $Perm.Write
        $Perm.No)
      $Perm.No)))
; Done precomputing, updating quantified heap chunks
; Chunk depleted?
(set-option :timeout 500)
(push) ; 5
(assert (not (forall (($r $Ref)) (!
  (=
    (-
      (ite
        (and (<= 0 (invOf@47 $r)) (< (invOf@47 $r) $t@43))
        $Perm.Write
        $Perm.No)
      ($permsTaken1 $r))
    $Perm.No)
  ))))
(check-sat)
; unknown
(pop) ; 5
; 0.00s
; (get-info :all-statistics)
; Enough permissions taken?
(set-option :timeout 500)
(push) ; 5
(assert (not (= (- $Perm.Write ($permsTaken1 ($Seq.index $t@41 i@30))) $Perm.No)))
(check-sat)
; unsat
(pop) ; 5
; 0.00s
; (get-info :all-statistics)
; Final check that enough permissions have been taken
; Done splitting
(declare-const fvf@51 $FVF<Bool>)
(assert (= ($FVF.lookup_Ref__Boolean_value fvf@51 ($Seq.index $t@41 i@30)) false))
(assert ($Set.equal
  ($FVF.domain_Ref__Boolean_value fvf@51)
  ($Set.singleton  ($Seq.index $t@41 i@30))))
; [exec]
; i := i + 1
; [eval] i + 1
; [eval] (0 <= i) && (i <= max)
; [eval] 0 <= i
(push) ; 5
(set-option :timeout 0)
(push) ; 6
(assert (not (not (<= 0 (+ i@30 1)))))
(check-sat)
; unknown
(pop) ; 6
; 0.00s
; (get-info :all-statistics)
(set-option :timeout 0)
(push) ; 6
(assert (not (<= 0 (+ i@30 1))))
(check-sat)
; unsat
(pop) ; 6
; 0.00s
; (get-info :all-statistics)
(push) ; 6
; [then-branch 9] 0 <= i@30 + 1
(assert (<= 0 (+ i@30 1)))
; [eval] i <= max
(pop) ; 6
; [dead else-branch 9] !0 <= i@30 + 1
(pop) ; 5
(set-option :timeout 0)
(push) ; 5
(assert (not (and (<= 0 (+ i@30 1)) (<= (+ i@30 1) max@1))))
(check-sat)
; unsat
(pop) ; 5
; 0.00s
; (get-info :all-statistics)
(assert (and (<= 0 (+ i@30 1)) (<= (+ i@30 1) max@1)))
(declare-const $k@52 $Perm)
(assert ($Perm.isValidVar $k@52))
(assert ($Perm.isReadVar $k@52 $Perm.Write))
(set-option :timeout 0)
(push) ; 5
(assert (not (or (= $k@52 $Perm.No) true)))
(check-sat)
; unsat
(pop) ; 5
; 0.00s
; (get-info :all-statistics)
(assert (< $k@52 $k@44))
; [eval] diz.Set__max > 0
(declare-const $k@53 $Perm)
(assert ($Perm.isValidVar $k@53))
(assert ($Perm.isReadVar $k@53 $Perm.Write))
(set-option :timeout 0)
(push) ; 5
(assert (not (or (= $k@53 $Perm.No) true)))
(check-sat)
; unsat
(pop) ; 5
; 0.00s
; (get-info :all-statistics)
(assert (< $k@53 $k@45))
; [eval] |diz.Set__contents| == diz.Set__max
; [eval] |diz.Set__contents|
(declare-const fvf@54 $FVF<Int>)
(declare-const fvf@55 $FVF<$Seq<$Ref>>)
(assert (= ($FVF.lookup_Set__max fvf@54 diz@20) $t@43))
(assert ($Set.equal ($FVF.domain_Set__max fvf@54) ($Set.singleton  diz@20)))
(assert ($Seq.equal ($FVF.lookup_Set__contents fvf@55 diz@20) $t@41))
(assert ($Set.equal ($FVF.domain_Set__contents fvf@55) ($Set.singleton  diz@20)))
(declare-const k@56 Int)
; [eval] (0 <= k) && (k < diz.Set__max)
; [eval] 0 <= k
(push) ; 5
(set-option :timeout 0)
(push) ; 6
(assert (not (not (<= 0 k@56))))
(check-sat)
; unknown
(pop) ; 6
; 0.00s
; (get-info :all-statistics)
(set-option :timeout 0)
(push) ; 6
(assert (not (<= 0 k@56)))
(check-sat)
; unknown
(pop) ; 6
; 0.00s
; (get-info :all-statistics)
(push) ; 6
; [then-branch 10] 0 <= k@56
(assert (<= 0 k@56))
; [eval] k < diz.Set__max
(set-option :timeout 0)
(push) ; 7
(assert (not (< $Perm.No $k@44)))
(check-sat)
; unsat
(pop) ; 7
; 0.00s
; (get-info :all-statistics)
(declare-const fvf@57 $FVF<Int>)
(assert (implies
  (< $Perm.No $k@44)
  (= ($FVF.lookup_Set__max fvf@57 diz@20) ($FVF.lookup_Set__max fvf@54 diz@20))))
(assert ($Set.equal ($FVF.domain_Set__max fvf@57) ($Set.singleton  diz@20)))
(pop) ; 6
(push) ; 6
; [else-branch 10] !0 <= k@56
(assert (not (<= 0 k@56)))
(pop) ; 6
(pop) ; 5
(assert ($Set.equal ($FVF.domain_Set__max fvf@57) ($Set.singleton  diz@20)))
(assert (implies
  (< $Perm.No $k@44)
  (= ($FVF.lookup_Set__max fvf@57 diz@20) ($FVF.lookup_Set__max fvf@54 diz@20))))
(set-option :timeout 0)
(push) ; 5
(assert (not (not (and (<= 0 k@56) (< k@56 ($FVF.lookup_Set__max fvf@57 diz@20))))))
(check-sat)
; unknown
(pop) ; 5
; 0.00s
; (get-info :all-statistics)
(assert (and (<= 0 k@56) (< k@56 ($FVF.lookup_Set__max fvf@57 diz@20))))
; [eval] diz.Set__contents[k]
(set-option :timeout 0)
(push) ; 5
(assert (not (< $Perm.No $k@45)))
(check-sat)
; unsat
(pop) ; 5
; 0.00s
; (get-info :all-statistics)
(declare-const fvf@58 $FVF<$Seq<$Ref>>)
(assert (implies
  (< $Perm.No $k@45)
  ($Seq.equal
    ($FVF.lookup_Set__contents fvf@58 diz@20)
    ($FVF.lookup_Set__contents fvf@55 diz@20))))
(assert ($Set.equal ($FVF.domain_Set__contents fvf@58) ($Set.singleton  diz@20)))
(set-option :timeout 0)
(push) ; 5
(assert (not (forall (($x Int) ($y Int)) (!
  (implies
    (and
      (and (<= 0 $x) (< $x ($FVF.lookup_Set__max fvf@57 diz@20)))
      (and (<= 0 $y) (< $y ($FVF.lookup_Set__max fvf@57 diz@20)))
      (=
        ($Seq.index ($FVF.lookup_Set__contents fvf@58 diz@20) $x)
        ($Seq.index ($FVF.lookup_Set__contents fvf@58 diz@20) $y)))
    (= $x $y))
  :pattern (($Seq.index ($FVF.lookup_Set__contents fvf@58 diz@20) $x) ($Seq.index
    ($FVF.lookup_Set__contents fvf@58 diz@20)
    $y))))))
(check-sat)
; unsat
(pop) ; 5
; 0.00s
; (get-info :all-statistics)
(declare-fun invOf@59 ($Ref) Int)
(assert (forall (($r $Ref)) (!
  (implies
    (and
      (<= 0 (invOf@59 $r))
      (< (invOf@59 $r) ($FVF.lookup_Set__max fvf@57 diz@20)))
    (= ($Seq.index ($FVF.lookup_Set__contents fvf@58 diz@20) (invOf@59 $r)) $r))
  :pattern ((invOf@59 $r)))))
(assert (forall ((k@56 Int)) (!
  (implies
    (and (<= 0 k@56) (< k@56 ($FVF.lookup_Set__max fvf@57 diz@20)))
    (=
      (invOf@59 ($Seq.index ($FVF.lookup_Set__contents fvf@58 diz@20) k@56))
      k@56))
  :pattern (($Seq.index ($FVF.lookup_Set__contents fvf@58 diz@20) k@56)))))
(declare-const fvf@60 $FVF<Bool>)
; Precomputing split data for Lookup(Set__contents,fvf@58,diz@20)[k@56].Ref__Boolean_value # W
(define-fun $permsTaken2 (($r $Ref)) $Perm
  ($Perm.min
    (ite
      (and
        (<= 0 (invOf@59 $r))
        (< (invOf@59 $r) ($FVF.lookup_Set__max fvf@57 diz@20)))
      $Perm.Write
      $Perm.No)
    (ite
      (= $r ($Seq.index ($FVF.lookup_Set__contents fvf@58 diz@20) k@56))
      (ite (= $r ($Seq.index $t@41 i@30)) $Perm.Write $Perm.No)
      $Perm.No)))
(define-fun $permsTaken3 (($r $Ref)) $Perm
  ($Perm.min
    (-
      (ite
        (and
          (<= 0 (invOf@59 $r))
          (< (invOf@59 $r) ($FVF.lookup_Set__max fvf@57 diz@20)))
        $Perm.Write
        $Perm.No)
      ($permsTaken2 $r))
    (ite
      (= $r ($Seq.index ($FVF.lookup_Set__contents fvf@58 diz@20) k@56))
      (-
        (ite
          (and (<= 0 (invOf@47 $r)) (< (invOf@47 $r) $t@43))
          $Perm.Write
          $Perm.No)
        ($permsTaken1 $r))
      $Perm.No)))
; Done precomputing, updating quantified heap chunks
; Chunk depleted?
(set-option :timeout 500)
(push) ; 5
(assert (not (forall (($r $Ref)) (!
  (=
    (-
      (ite (= $r ($Seq.index $t@41 i@30)) $Perm.Write $Perm.No)
      ($permsTaken2 $r))
    $Perm.No)
  ))))
(check-sat)
; unknown
(pop) ; 5
; 0.00s
; (get-info :all-statistics)
; Enough permissions taken?
(set-option :timeout 500)
(push) ; 5
(assert (not (=
  (-
    (ite
      (and
        (<=
          0
          (invOf@59 ($Seq.index ($FVF.lookup_Set__contents fvf@58 diz@20) k@56)))
        (<
          (invOf@59 ($Seq.index ($FVF.lookup_Set__contents fvf@58 diz@20) k@56))
          ($FVF.lookup_Set__max fvf@57 diz@20)))
      $Perm.Write
      $Perm.No)
    ($permsTaken2 ($Seq.index ($FVF.lookup_Set__contents fvf@58 diz@20) k@56)))
  $Perm.No)))
(check-sat)
; unknown
(pop) ; 5
; 0.00s
; (get-info :all-statistics)
; Chunk depleted?
(set-option :timeout 500)
(push) ; 5
(assert (not (forall (($r $Ref)) (!
  (=
    (-
      (-
        (ite
          (and (<= 0 (invOf@47 $r)) (< (invOf@47 $r) $t@43))
          $Perm.Write
          $Perm.No)
        ($permsTaken1 $r))
      ($permsTaken3 $r))
    $Perm.No)
  ))))
(check-sat)
; unknown
(pop) ; 5
; 0.01s
; (get-info :all-statistics)
; Enough permissions taken?
(set-option :timeout 500)
(push) ; 5
(assert (not (=
  (-
    (-
      (ite
        (and
          (<=
            0
            (invOf@59 ($Seq.index ($FVF.lookup_Set__contents fvf@58 diz@20) k@56)))
          (<
            (invOf@59 ($Seq.index ($FVF.lookup_Set__contents fvf@58 diz@20) k@56))
            ($FVF.lookup_Set__max fvf@57 diz@20)))
        $Perm.Write
        $Perm.No)
      ($permsTaken2 ($Seq.index ($FVF.lookup_Set__contents fvf@58 diz@20) k@56)))
    ($permsTaken3 ($Seq.index ($FVF.lookup_Set__contents fvf@58 diz@20) k@56)))
  $Perm.No)))
(check-sat)
; unsat
(pop) ; 5
; 0.00s
; (get-info :all-statistics)
; Final check that enough permissions have been taken
; Done splitting
(assert (forall (($r $Ref)) (!
  (implies
    (and
      (<
        $Perm.No
        (-
          (ite
            (and (<= 0 (invOf@47 $r)) (< (invOf@47 $r) $t@43))
            $Perm.Write
            $Perm.No)
          ($permsTaken1 $r)))
      ($Set.in $r ($FVF.domain_Ref__Boolean_value fvf@60)))
    (=
      ($FVF.lookup_Ref__Boolean_value fvf@60 $r)
      ($FVF.lookup_Ref__Boolean_value $t@38 $r)))
  :pattern (($FVF.lookup_Ref__Boolean_value fvf@60 $r) (invOf@47 $r))
  :pattern (($FVF.lookup_Ref__Boolean_value $t@38 $r) (invOf@47 $r)))))
(assert (forall (($r $Ref)) (!
  (implies
    (and
      (= $r ($Seq.index $t@41 i@30))
      ($Set.in $r ($FVF.domain_Ref__Boolean_value fvf@60)))
    (=
      ($FVF.lookup_Ref__Boolean_value fvf@60 $r)
      ($FVF.lookup_Ref__Boolean_value fvf@51 $r)))
  :pattern (($FVF.lookup_Ref__Boolean_value fvf@60 $r))
  :pattern (($FVF.lookup_Ref__Boolean_value fvf@51 $r)))))
(assert (forall (($r $Ref)) (!
  (iff
    ($Set.in $r ($FVF.domain_Ref__Boolean_value fvf@60))
    (and
      (<= 0 (invOf@59 $r))
      (< (invOf@59 $r) ($FVF.lookup_Set__max fvf@57 diz@20))))
  :pattern (($Set.in $r ($FVF.domain_Ref__Boolean_value fvf@60))))))
; [eval] diz.Set__max == max
; [eval] (forall k: Int :: (0 <= k) && (k < i) ==> !diz.Set__contents[k].Ref__Boolean_value)
(declare-const k@61 Int)
(push) ; 5
; [eval] (0 <= k) && (k < i) ==> !diz.Set__contents[k].Ref__Boolean_value
; [eval] (0 <= k) && (k < i)
; [eval] 0 <= k
(push) ; 6
(set-option :timeout 0)
(push) ; 7
(assert (not (not (<= 0 k@61))))
(check-sat)
; unknown
(pop) ; 7
; 0.00s
; (get-info :all-statistics)
(set-option :timeout 0)
(push) ; 7
(assert (not (<= 0 k@61)))
(check-sat)
; unknown
(pop) ; 7
; 0.00s
; (get-info :all-statistics)
(push) ; 7
; [then-branch 11] 0 <= k@61
(assert (<= 0 k@61))
; [eval] k < i
(pop) ; 7
(push) ; 7
; [else-branch 11] !0 <= k@61
(assert (not (<= 0 k@61)))
(pop) ; 7
(pop) ; 6
(push) ; 6
(set-option :timeout 0)
(push) ; 7
(assert (not (not (and (<= 0 k@61) (< k@61 (+ i@30 1))))))
(check-sat)
; unknown
(pop) ; 7
; 0.00s
; (get-info :all-statistics)
(set-option :timeout 0)
(push) ; 7
(assert (not (and (<= 0 k@61) (< k@61 (+ i@30 1)))))
(check-sat)
; unknown
(pop) ; 7
; 0.00s
; (get-info :all-statistics)
(push) ; 7
; [then-branch 12] 0 <= k@61 && k@61 < i@30 + 1
(assert (and (<= 0 k@61) (< k@61 (+ i@30 1))))
; [eval] !diz.Set__contents[k].Ref__Boolean_value
; [eval] diz.Set__contents[k]
(set-option :timeout 0)
(push) ; 8
(assert (not (not (= ($Seq.index $t@41 k@61) $Ref.null))))
(check-sat)
; unsat
(pop) ; 8
; 0.00s
; (get-info :all-statistics)
(set-option :timeout 0)
(push) ; 8
(assert (not (<
  $Perm.No
  (+
    (-
      (ite
        (and
          (<= 0 (invOf@47 ($Seq.index $t@41 k@61)))
          (< (invOf@47 ($Seq.index $t@41 k@61)) $t@43))
        $Perm.Write
        $Perm.No)
      ($permsTaken1 ($Seq.index $t@41 k@61)))
    (ite
      (= ($Seq.index $t@41 k@61) ($Seq.index $t@41 i@30))
      $Perm.Write
      $Perm.No)))))
(check-sat)
; unsat
(pop) ; 8
; 0.00s
; (get-info :all-statistics)
(declare-const fvf@62 $FVF<Bool>)
(assert (forall (($r $Ref)) (!
  (implies
    (and
      (<
        $Perm.No
        (-
          (ite
            (and (<= 0 (invOf@47 $r)) (< (invOf@47 $r) $t@43))
            $Perm.Write
            $Perm.No)
          ($permsTaken1 $r)))
      ($Set.in $r ($FVF.domain_Ref__Boolean_value fvf@62)))
    (=
      ($FVF.lookup_Ref__Boolean_value fvf@62 $r)
      ($FVF.lookup_Ref__Boolean_value $t@38 $r)))
  :pattern (($FVF.lookup_Ref__Boolean_value fvf@62 $r) (invOf@47 $r))
  :pattern (($FVF.lookup_Ref__Boolean_value $t@38 $r) (invOf@47 $r)))))
(assert (forall (($r $Ref)) (!
  (implies
    (and
      (= $r ($Seq.index $t@41 i@30))
      ($Set.in $r ($FVF.domain_Ref__Boolean_value fvf@62)))
    (=
      ($FVF.lookup_Ref__Boolean_value fvf@62 $r)
      ($FVF.lookup_Ref__Boolean_value fvf@51 $r)))
  :pattern (($FVF.lookup_Ref__Boolean_value fvf@62 $r))
  :pattern (($FVF.lookup_Ref__Boolean_value fvf@51 $r)))))
(assert (forall ((k@61 Int)) (!
  (iff
    ($Set.in ($Seq.index $t@41 k@61) ($FVF.domain_Ref__Boolean_value fvf@62))
    (and (<= 0 k@61) (< k@61 (+ i@30 1))))
  :pattern (($Set.in
    ($Seq.index $t@41 k@61)
    ($FVF.domain_Ref__Boolean_value fvf@62))))))
(pop) ; 7
(push) ; 7
; [else-branch 12] !0 <= k@61 && k@61 < i@30 + 1
(assert (not (and (<= 0 k@61) (< k@61 (+ i@30 1)))))
(pop) ; 7
(pop) ; 6
(assert (forall ((k@61 Int)) (!
  (iff
    ($Set.in ($Seq.index $t@41 k@61) ($FVF.domain_Ref__Boolean_value fvf@62))
    (and (<= 0 k@61) (< k@61 (+ i@30 1))))
  :pattern (($Set.in
    ($Seq.index $t@41 k@61)
    ($FVF.domain_Ref__Boolean_value fvf@62))))))
(assert (forall (($r $Ref)) (!
  (implies
    (and
      (= $r ($Seq.index $t@41 i@30))
      ($Set.in $r ($FVF.domain_Ref__Boolean_value fvf@62)))
    (=
      ($FVF.lookup_Ref__Boolean_value fvf@62 $r)
      ($FVF.lookup_Ref__Boolean_value fvf@51 $r)))
  :pattern (($FVF.lookup_Ref__Boolean_value fvf@62 $r))
  :pattern (($FVF.lookup_Ref__Boolean_value fvf@51 $r)))))
(assert (forall (($r $Ref)) (!
  (implies
    (and
      (<
        $Perm.No
        (-
          (ite
            (and (<= 0 (invOf@47 $r)) (< (invOf@47 $r) $t@43))
            $Perm.Write
            $Perm.No)
          ($permsTaken1 $r)))
      ($Set.in $r ($FVF.domain_Ref__Boolean_value fvf@62)))
    (=
      ($FVF.lookup_Ref__Boolean_value fvf@62 $r)
      ($FVF.lookup_Ref__Boolean_value $t@38 $r)))
  :pattern (($FVF.lookup_Ref__Boolean_value fvf@62 $r) (invOf@47 $r))
  :pattern (($FVF.lookup_Ref__Boolean_value $t@38 $r) (invOf@47 $r)))))
(pop) ; 5
(assert (forall ((k@61 Int)) (!
  (iff
    ($Set.in ($Seq.index $t@41 k@61) ($FVF.domain_Ref__Boolean_value fvf@62))
    (and (<= 0 k@61) (< k@61 (+ i@30 1))))
  :pattern (($Set.in
    ($Seq.index $t@41 k@61)
    ($FVF.domain_Ref__Boolean_value fvf@62))))))
(assert (forall (($r $Ref)) (!
  (implies
    (and
      (= $r ($Seq.index $t@41 i@30))
      ($Set.in $r ($FVF.domain_Ref__Boolean_value fvf@62)))
    (=
      ($FVF.lookup_Ref__Boolean_value fvf@62 $r)
      ($FVF.lookup_Ref__Boolean_value fvf@51 $r)))
  :pattern (($FVF.lookup_Ref__Boolean_value fvf@62 $r))
  :pattern (($FVF.lookup_Ref__Boolean_value fvf@51 $r)))))
(assert (forall (($r $Ref)) (!
  (implies
    (and
      (<
        $Perm.No
        (-
          (ite
            (and (<= 0 (invOf@47 $r)) (< (invOf@47 $r) $t@43))
            $Perm.Write
            $Perm.No)
          ($permsTaken1 $r)))
      ($Set.in $r ($FVF.domain_Ref__Boolean_value fvf@62)))
    (=
      ($FVF.lookup_Ref__Boolean_value fvf@62 $r)
      ($FVF.lookup_Ref__Boolean_value $t@38 $r)))
  :pattern (($FVF.lookup_Ref__Boolean_value fvf@62 $r) (invOf@47 $r))
  :pattern (($FVF.lookup_Ref__Boolean_value $t@38 $r) (invOf@47 $r)))))
(set-option :timeout 0)
(push) ; 5
(assert (not (forall ((k@61 Int)) (!
  (implies
    (and (<= 0 k@61) (< k@61 (+ i@30 1)))
    (not ($FVF.lookup_Ref__Boolean_value fvf@62 ($Seq.index $t@41 k@61))))
  :pattern (($Seq.index $t@41 k@61))))))
(check-sat)
; unsat
(pop) ; 5
; 0.00s
; (get-info :all-statistics)
(assert (forall ((k@61 Int)) (!
  (implies
    (and (<= 0 k@61) (< k@61 (+ i@30 1)))
    (not ($FVF.lookup_Ref__Boolean_value fvf@62 ($Seq.index $t@41 k@61))))
  :pattern (($Seq.index $t@41 k@61)))))
(pop) ; 4
(push) ; 4
; Establish loop invariant
; [eval] (0 <= i) && (i <= max)
; [eval] 0 <= i
(push) ; 5
(set-option :timeout 0)
(push) ; 6
(assert (not false))
(check-sat)
; unknown
(pop) ; 6
; 0.00s
; (get-info :all-statistics)
(push) ; 6
; [then-branch 13] True
; [eval] i <= max
(pop) ; 6
; [dead else-branch 13] False
(pop) ; 5
(set-option :timeout 0)
(push) ; 5
(assert (not (<= 0 max@1)))
(check-sat)
; unsat
(pop) ; 5
; 0.00s
; (get-info :all-statistics)
(assert (<= 0 max@1))
(declare-const $k@63 $Perm)
(assert ($Perm.isValidVar $k@63))
(assert ($Perm.isReadVar $k@63 $Perm.Write))
(set-option :timeout 0)
(push) ; 5
(assert (not (or (= $k@63 $Perm.No) true)))
(check-sat)
; unsat
(pop) ; 5
; 0.00s
; (get-info :all-statistics)
(assert (< $k@63 $Perm.Write))
; [eval] diz.Set__max > 0
(declare-const $k@64 $Perm)
(assert ($Perm.isValidVar $k@64))
(assert ($Perm.isReadVar $k@64 $Perm.Write))
(set-option :timeout 0)
(push) ; 5
(assert (not (or (= $k@64 $Perm.No) true)))
(check-sat)
; unsat
(pop) ; 5
; 0.00s
; (get-info :all-statistics)
(assert (< $k@64 $Perm.Write))
; [eval] |diz.Set__contents| == diz.Set__max
; [eval] |diz.Set__contents|
(declare-const fvf@65 $FVF<Int>)
(declare-const fvf@66 $FVF<$Seq<$Ref>>)
(assert (= ($FVF.lookup_Set__max fvf@65 diz@20) max@1))
(assert ($Set.equal ($FVF.domain_Set__max fvf@65) ($Set.singleton  diz@20)))
(assert ($Seq.equal ($FVF.lookup_Set__contents fvf@66 diz@20) sys__result@25))
(assert ($Set.equal ($FVF.domain_Set__contents fvf@66) ($Set.singleton  diz@20)))
(declare-const k@67 Int)
; [eval] (0 <= k) && (k < diz.Set__max)
; [eval] 0 <= k
(push) ; 5
(set-option :timeout 0)
(push) ; 6
(assert (not (not (<= 0 k@67))))
(check-sat)
; unknown
(pop) ; 6
; 0.00s
; (get-info :all-statistics)
(set-option :timeout 0)
(push) ; 6
(assert (not (<= 0 k@67)))
(check-sat)
; unknown
(pop) ; 6
; 0.00s
; (get-info :all-statistics)
(push) ; 6
; [then-branch 14] 0 <= k@67
(assert (<= 0 k@67))
; [eval] k < diz.Set__max
(declare-const fvf@68 $FVF<Int>)
(assert (= ($FVF.lookup_Set__max fvf@68 diz@20) ($FVF.lookup_Set__max fvf@65 diz@20)))
(assert ($Set.equal ($FVF.domain_Set__max fvf@68) ($Set.singleton  diz@20)))
(pop) ; 6
(push) ; 6
; [else-branch 14] !0 <= k@67
(assert (not (<= 0 k@67)))
(pop) ; 6
(pop) ; 5
(assert ($Set.equal ($FVF.domain_Set__max fvf@68) ($Set.singleton  diz@20)))
(assert (= ($FVF.lookup_Set__max fvf@68 diz@20) ($FVF.lookup_Set__max fvf@65 diz@20)))
(set-option :timeout 0)
(push) ; 5
(assert (not (not (and (<= 0 k@67) (< k@67 ($FVF.lookup_Set__max fvf@68 diz@20))))))
(check-sat)
; unknown
(pop) ; 5
; 0.00s
; (get-info :all-statistics)
(assert (and (<= 0 k@67) (< k@67 ($FVF.lookup_Set__max fvf@68 diz@20))))
; [eval] diz.Set__contents[k]
(declare-const fvf@69 $FVF<$Seq<$Ref>>)
(assert ($Seq.equal
  ($FVF.lookup_Set__contents fvf@69 diz@20)
  ($FVF.lookup_Set__contents fvf@66 diz@20)))
(assert ($Set.equal ($FVF.domain_Set__contents fvf@69) ($Set.singleton  diz@20)))
(set-option :timeout 0)
(push) ; 5
(assert (not (forall (($x Int) ($y Int)) (!
  (implies
    (and
      (and (<= 0 $x) (< $x ($FVF.lookup_Set__max fvf@68 diz@20)))
      (and (<= 0 $y) (< $y ($FVF.lookup_Set__max fvf@68 diz@20)))
      (=
        ($Seq.index ($FVF.lookup_Set__contents fvf@69 diz@20) $x)
        ($Seq.index ($FVF.lookup_Set__contents fvf@69 diz@20) $y)))
    (= $x $y))
  :pattern (($Seq.index ($FVF.lookup_Set__contents fvf@69 diz@20) $x) ($Seq.index
    ($FVF.lookup_Set__contents fvf@69 diz@20)
    $y))))))
(check-sat)
; unsat
(pop) ; 5
; 0.00s
; (get-info :all-statistics)
(declare-fun invOf@70 ($Ref) Int)
(assert (forall (($r $Ref)) (!
  (implies
    (and
      (<= 0 (invOf@70 $r))
      (< (invOf@70 $r) ($FVF.lookup_Set__max fvf@68 diz@20)))
    (= ($Seq.index ($FVF.lookup_Set__contents fvf@69 diz@20) (invOf@70 $r)) $r))
  :pattern ((invOf@70 $r)))))
(assert (forall ((k@67 Int)) (!
  (implies
    (and (<= 0 k@67) (< k@67 ($FVF.lookup_Set__max fvf@68 diz@20)))
    (=
      (invOf@70 ($Seq.index ($FVF.lookup_Set__contents fvf@69 diz@20) k@67))
      k@67))
  :pattern (($Seq.index ($FVF.lookup_Set__contents fvf@69 diz@20) k@67)))))
(declare-const fvf@71 $FVF<Bool>)
; Precomputing split data for Lookup(Set__contents,fvf@69,diz@20)[k@67].Ref__Boolean_value # W
(define-fun $permsTaken4 (($r $Ref)) $Perm
  ($Perm.min
    (ite
      (and
        (<= 0 (invOf@70 $r))
        (< (invOf@70 $r) ($FVF.lookup_Set__max fvf@68 diz@20)))
      $Perm.Write
      $Perm.No)
    (ite
      (= $r ($Seq.index ($FVF.lookup_Set__contents fvf@69 diz@20) k@67))
      (ite
        (and (<= 0 (invOf@29 $r)) (< (invOf@29 $r) ($Seq.length sys__result@25)))
        $Perm.Write
        $Perm.No)
      $Perm.No)))
; Done precomputing, updating quantified heap chunks
; Chunk depleted?
(set-option :timeout 500)
(push) ; 5
(assert (not (forall (($r $Ref)) (!
  (=
    (-
      (ite
        (and (<= 0 (invOf@29 $r)) (< (invOf@29 $r) ($Seq.length sys__result@25)))
        $Perm.Write
        $Perm.No)
      ($permsTaken4 $r))
    $Perm.No)
  ))))
(check-sat)
; unknown
(pop) ; 5
; 0.00s
; (get-info :all-statistics)
; Enough permissions taken?
(set-option :timeout 500)
(push) ; 5
(assert (not (=
  (-
    (ite
      (and
        (<=
          0
          (invOf@70 ($Seq.index ($FVF.lookup_Set__contents fvf@69 diz@20) k@67)))
        (<
          (invOf@70 ($Seq.index ($FVF.lookup_Set__contents fvf@69 diz@20) k@67))
          ($FVF.lookup_Set__max fvf@68 diz@20)))
      $Perm.Write
      $Perm.No)
    ($permsTaken4 ($Seq.index ($FVF.lookup_Set__contents fvf@69 diz@20) k@67)))
  $Perm.No)))
(check-sat)
; unsat
(pop) ; 5
; 0.00s
; (get-info :all-statistics)
; Final check that enough permissions have been taken
; Done splitting
(assert (forall (($r $Ref)) (!
  (implies
    (and
      (and (<= 0 (invOf@29 $r)) (< (invOf@29 $r) ($Seq.length sys__result@25)))
      ($Set.in $r ($FVF.domain_Ref__Boolean_value fvf@71)))
    (=
      ($FVF.lookup_Ref__Boolean_value fvf@71 $r)
      ($FVF.lookup_Ref__Boolean_value $t@27 $r)))
  :pattern (($FVF.lookup_Ref__Boolean_value fvf@71 $r) (invOf@29 $r))
  :pattern (($FVF.lookup_Ref__Boolean_value $t@27 $r) (invOf@29 $r)))))
(assert (forall (($r $Ref)) (!
  (iff
    ($Set.in $r ($FVF.domain_Ref__Boolean_value fvf@71))
    (and
      (<= 0 (invOf@70 $r))
      (< (invOf@70 $r) ($FVF.lookup_Set__max fvf@68 diz@20))))
  :pattern (($Set.in $r ($FVF.domain_Ref__Boolean_value fvf@71))))))
; [eval] diz.Set__max == max
; [eval] (forall k: Int :: (0 <= k) && (k < i) ==> !diz.Set__contents[k].Ref__Boolean_value)
(declare-const k@72 Int)
(push) ; 5
; [eval] (0 <= k) && (k < i) ==> !diz.Set__contents[k].Ref__Boolean_value
; [eval] (0 <= k) && (k < i)
; [eval] 0 <= k
(push) ; 6
(set-option :timeout 0)
(push) ; 7
(assert (not (not (<= 0 k@72))))
(check-sat)
; unknown
(pop) ; 7
; 0.00s
; (get-info :all-statistics)
(set-option :timeout 0)
(push) ; 7
(assert (not (<= 0 k@72)))
(check-sat)
; unknown
(pop) ; 7
; 0.00s
; (get-info :all-statistics)
(push) ; 7
; [then-branch 15] 0 <= k@72
(assert (<= 0 k@72))
; [eval] k < i
(pop) ; 7
(push) ; 7
; [else-branch 15] !0 <= k@72
(assert (not (<= 0 k@72)))
(pop) ; 7
(pop) ; 6
(push) ; 6
(set-option :timeout 0)
(push) ; 7
(assert (not (not (and (<= 0 k@72) (< k@72 0)))))
(check-sat)
; unsat
(pop) ; 7
; 0.00s
; (get-info :all-statistics)
(set-option :timeout 0)
(push) ; 7
(assert (not (and (<= 0 k@72) (< k@72 0))))
(check-sat)
; unknown
(pop) ; 7
; 0.00s
; (get-info :all-statistics)
; [dead then-branch 16] 0 <= k@72 && k@72 < 0
(push) ; 7
; [else-branch 16] !0 <= k@72 && k@72 < 0
(assert (not (and (<= 0 k@72) (< k@72 0))))
(pop) ; 7
(pop) ; 6
(pop) ; 5
(set-option :timeout 0)
(push) ; 5
(assert (not (forall ((k@72 Int)) (!
  true
  :pattern ()))))
(check-sat)
; unsat
(pop) ; 5
; 0.00s
; (get-info :all-statistics)
(assert (forall ((k@72 Int)) (!
  true
  :pattern ())))
; Continue after loop
(declare-const $t@73 $Snap)
(declare-const $t@74 $Snap)
(assert (= $t@73 ($Snap.combine $t@74 $Snap.unit)))
(declare-const $t@75 $Snap)
(assert (= $t@74 ($Snap.combine $t@75 $Snap.unit)))
(declare-const $t@76 $Snap)
(assert (= $t@75 ($Snap.combine $t@76 $Snap.unit)))
(declare-const $t@77 $Snap)
(declare-const $t@78 $FVF<Bool>)
(assert (= $t@76 ($Snap.combine $t@77 ($SortWrappers.$FVF<Bool>To$Snap $t@78))))
(declare-const $t@79 $Snap)
(assert (= $t@77 ($Snap.combine $t@79 $Snap.unit)))
(declare-const $t@80 Int)
(declare-const $t@81 $Seq<$Ref>)
(assert (=
  $t@79
  ($Snap.combine
    ($SortWrappers.IntTo$Snap $t@80)
    ($SortWrappers.$Seq<$Ref>To$Snap $t@81))))
(declare-const $t@82 Int)
(assert (=
  ($SortWrappers.IntTo$Snap $t@80)
  ($Snap.combine ($SortWrappers.IntTo$Snap $t@82) $Snap.unit)))
(declare-const $t@83 Int)
(assert (=
  ($SortWrappers.IntTo$Snap $t@82)
  ($Snap.combine $Snap.unit ($SortWrappers.IntTo$Snap $t@83))))
; [eval] (0 <= i) && (i <= max)
; [eval] 0 <= i
(push) ; 5
(set-option :timeout 0)
(push) ; 6
(assert (not (not (<= 0 i@30))))
(check-sat)
; unknown
(pop) ; 6
; 0.01s
; (get-info :all-statistics)
(set-option :timeout 0)
(push) ; 6
(assert (not (<= 0 i@30)))
(check-sat)
; unknown
(pop) ; 6
; 0.00s
; (get-info :all-statistics)
(push) ; 6
; [then-branch 17] 0 <= i@30
(assert (<= 0 i@30))
; [eval] i <= max
(pop) ; 6
(push) ; 6
; [else-branch 17] !0 <= i@30
(assert (not (<= 0 i@30)))
(pop) ; 6
(pop) ; 5
(assert (and (<= 0 i@30) (<= i@30 max@1)))
(declare-const $k@84 $Perm)
(assert ($Perm.isValidVar $k@84))
(assert ($Perm.isReadVar $k@84 $Perm.Write))
(assert (implies (< $Perm.No (- $Perm.Write $k@63)) (= $t@83 max@1)))
; [eval] diz.Set__max > 0
(set-option :timeout 0)
(push) ; 5
(assert (not (not (= (+ (- $Perm.Write $k@63) $k@84) $Perm.No))))
(check-sat)
; unsat
(pop) ; 5
; 0.00s
; (get-info :all-statistics)
(assert (not (= (+ (- $Perm.Write $k@63) $k@84) $Perm.No)))
(assert (> $t@83 0))
(declare-const $k@85 $Perm)
(assert ($Perm.isValidVar $k@85))
(assert ($Perm.isReadVar $k@85 $Perm.Write))
(assert (implies (< $Perm.No (- $Perm.Write $k@64)) ($Seq.equal $t@81 sys__result@25)))
; [eval] |diz.Set__contents| == diz.Set__max
; [eval] |diz.Set__contents|
(set-option :timeout 0)
(push) ; 5
(assert (not (not (= (+ (- $Perm.Write $k@64) $k@85) $Perm.No))))
(check-sat)
; unsat
(pop) ; 5
; 0.00s
; (get-info :all-statistics)
(assert (not (= (+ (- $Perm.Write $k@64) $k@85) $Perm.No)))
(assert (= ($Seq.length $t@81) $t@83))
(declare-const k@86 Int)
(push) ; 5
; [eval] (0 <= k) && (k < diz.Set__max)
; [eval] 0 <= k
(push) ; 6
(set-option :timeout 0)
(push) ; 7
(assert (not (not (<= 0 k@86))))
(check-sat)
; unknown
(pop) ; 7
; 0.00s
; (get-info :all-statistics)
(set-option :timeout 0)
(push) ; 7
(assert (not (<= 0 k@86)))
(check-sat)
; unknown
(pop) ; 7
; 0.00s
; (get-info :all-statistics)
(push) ; 7
; [then-branch 18] 0 <= k@86
(assert (<= 0 k@86))
; [eval] k < diz.Set__max
(pop) ; 7
(push) ; 7
; [else-branch 18] !0 <= k@86
(assert (not (<= 0 k@86)))
(pop) ; 7
(pop) ; 6
(assert (and (<= 0 k@86) (< k@86 $t@83)))
; [eval] diz.Set__contents[k]
(pop) ; 5
(declare-fun invOf@87 ($Ref) Int)
(assert (forall (($r $Ref)) (!
  (implies
    (and (<= 0 (invOf@87 $r)) (< (invOf@87 $r) $t@83))
    (= ($Seq.index $t@81 (invOf@87 $r)) $r))
  :pattern ((invOf@87 $r)))))
(assert (forall ((k@86 Int)) (!
  (implies
    (and (<= 0 k@86) (< k@86 $t@83))
    (= (invOf@87 ($Seq.index $t@81 k@86)) k@86))
  :pattern (($Seq.index $t@81 k@86)))))
(assert (forall ((k@86 Int)) (!
  (iff
    ($Set.in ($Seq.index $t@81 k@86) ($FVF.domain_Ref__Boolean_value $t@78))
    (and (<= 0 k@86) (< k@86 $t@83)))
  :pattern (($Set.in
    ($Seq.index $t@81 k@86)
    ($FVF.domain_Ref__Boolean_value $t@78))))))
(assert (forall ((k@86 Int)) (!
  (implies
    (and (<= 0 k@86) (< k@86 $t@83))
    (not (= ($Seq.index $t@81 k@86) $Ref.null)))
  :pattern (($Seq.index $t@81 k@86)))))
; [eval] diz.Set__max == max
(assert (= $t@83 max@1))
; [eval] (forall k: Int :: (0 <= k) && (k < i) ==> !diz.Set__contents[k].Ref__Boolean_value)
(declare-const k@88 Int)
(push) ; 5
; [eval] (0 <= k) && (k < i) ==> !diz.Set__contents[k].Ref__Boolean_value
; [eval] (0 <= k) && (k < i)
; [eval] 0 <= k
(push) ; 6
(set-option :timeout 0)
(push) ; 7
(assert (not (not (<= 0 k@88))))
(check-sat)
; unknown
(pop) ; 7
; 0.00s
; (get-info :all-statistics)
(set-option :timeout 0)
(push) ; 7
(assert (not (<= 0 k@88)))
(check-sat)
; unknown
(pop) ; 7
; 0.00s
; (get-info :all-statistics)
(push) ; 7
; [then-branch 19] 0 <= k@88
(assert (<= 0 k@88))
; [eval] k < i
(pop) ; 7
(push) ; 7
; [else-branch 19] !0 <= k@88
(assert (not (<= 0 k@88)))
(pop) ; 7
(pop) ; 6
(push) ; 6
(set-option :timeout 0)
(push) ; 7
(assert (not (not (and (<= 0 k@88) (< k@88 i@30)))))
(check-sat)
; unknown
(pop) ; 7
; 0.00s
; (get-info :all-statistics)
(set-option :timeout 0)
(push) ; 7
(assert (not (and (<= 0 k@88) (< k@88 i@30))))
(check-sat)
; unknown
(pop) ; 7
; 0.00s
; (get-info :all-statistics)
(push) ; 7
; [then-branch 20] 0 <= k@88 && k@88 < i@30
(assert (and (<= 0 k@88) (< k@88 i@30)))
; [eval] !diz.Set__contents[k].Ref__Boolean_value
; [eval] diz.Set__contents[k]
(set-option :timeout 0)
(push) ; 8
(assert (not (not (= ($Seq.index $t@81 k@88) $Ref.null))))
(check-sat)
; unsat
(pop) ; 8
; 0.00s
; (get-info :all-statistics)
(set-option :timeout 0)
(push) ; 8
(assert (not (<
  $Perm.No
  (+
    (-
      (ite
        (and
          (<= 0 (invOf@29 ($Seq.index $t@81 k@88)))
          (< (invOf@29 ($Seq.index $t@81 k@88)) ($Seq.length sys__result@25)))
        $Perm.Write
        $Perm.No)
      ($permsTaken4 ($Seq.index $t@81 k@88)))
    (ite
      (and
        (<= 0 (invOf@87 ($Seq.index $t@81 k@88)))
        (< (invOf@87 ($Seq.index $t@81 k@88)) $t@83))
      $Perm.Write
      $Perm.No)))))
(check-sat)
; unsat
(pop) ; 8
; 0.00s
; (get-info :all-statistics)
(declare-const fvf@89 $FVF<Bool>)
(assert (forall (($r $Ref)) (!
  (implies
    (and
      (<
        $Perm.No
        (-
          (ite
            (and
              (<= 0 (invOf@29 $r))
              (< (invOf@29 $r) ($Seq.length sys__result@25)))
            $Perm.Write
            $Perm.No)
          ($permsTaken4 $r)))
      ($Set.in $r ($FVF.domain_Ref__Boolean_value fvf@89)))
    (=
      ($FVF.lookup_Ref__Boolean_value fvf@89 $r)
      ($FVF.lookup_Ref__Boolean_value $t@27 $r)))
  :pattern (($FVF.lookup_Ref__Boolean_value fvf@89 $r) (invOf@29 $r))
  :pattern (($FVF.lookup_Ref__Boolean_value $t@27 $r) (invOf@29 $r)))))
(assert (forall (($r $Ref)) (!
  (implies
    (and
      (and (<= 0 (invOf@87 $r)) (< (invOf@87 $r) $t@83))
      ($Set.in $r ($FVF.domain_Ref__Boolean_value fvf@89)))
    (=
      ($FVF.lookup_Ref__Boolean_value fvf@89 $r)
      ($FVF.lookup_Ref__Boolean_value $t@78 $r)))
  :pattern (($FVF.lookup_Ref__Boolean_value fvf@89 $r) (invOf@87 $r))
  :pattern (($FVF.lookup_Ref__Boolean_value $t@78 $r) (invOf@87 $r)))))
(assert (forall ((k@88 Int)) (!
  (iff
    ($Set.in ($Seq.index $t@81 k@88) ($FVF.domain_Ref__Boolean_value fvf@89))
    (and (<= 0 k@88) (< k@88 i@30)))
  :pattern (($Set.in
    ($Seq.index $t@81 k@88)
    ($FVF.domain_Ref__Boolean_value fvf@89))))))
(pop) ; 7
(push) ; 7
; [else-branch 20] !0 <= k@88 && k@88 < i@30
(assert (not (and (<= 0 k@88) (< k@88 i@30))))
(pop) ; 7
(pop) ; 6
(assert (forall ((k@88 Int)) (!
  (iff
    ($Set.in ($Seq.index $t@81 k@88) ($FVF.domain_Ref__Boolean_value fvf@89))
    (and (<= 0 k@88) (< k@88 i@30)))
  :pattern (($Set.in
    ($Seq.index $t@81 k@88)
    ($FVF.domain_Ref__Boolean_value fvf@89))))))
(assert (forall (($r $Ref)) (!
  (implies
    (and
      (and (<= 0 (invOf@87 $r)) (< (invOf@87 $r) $t@83))
      ($Set.in $r ($FVF.domain_Ref__Boolean_value fvf@89)))
    (=
      ($FVF.lookup_Ref__Boolean_value fvf@89 $r)
      ($FVF.lookup_Ref__Boolean_value $t@78 $r)))
  :pattern (($FVF.lookup_Ref__Boolean_value fvf@89 $r) (invOf@87 $r))
  :pattern (($FVF.lookup_Ref__Boolean_value $t@78 $r) (invOf@87 $r)))))
(assert (forall (($r $Ref)) (!
  (implies
    (and
      (<
        $Perm.No
        (-
          (ite
            (and
              (<= 0 (invOf@29 $r))
              (< (invOf@29 $r) ($Seq.length sys__result@25)))
            $Perm.Write
            $Perm.No)
          ($permsTaken4 $r)))
      ($Set.in $r ($FVF.domain_Ref__Boolean_value fvf@89)))
    (=
      ($FVF.lookup_Ref__Boolean_value fvf@89 $r)
      ($FVF.lookup_Ref__Boolean_value $t@27 $r)))
  :pattern (($FVF.lookup_Ref__Boolean_value fvf@89 $r) (invOf@29 $r))
  :pattern (($FVF.lookup_Ref__Boolean_value $t@27 $r) (invOf@29 $r)))))
(pop) ; 5
(assert (forall ((k@88 Int)) (!
  (iff
    ($Set.in ($Seq.index $t@81 k@88) ($FVF.domain_Ref__Boolean_value fvf@89))
    (and (<= 0 k@88) (< k@88 i@30)))
  :pattern (($Set.in
    ($Seq.index $t@81 k@88)
    ($FVF.domain_Ref__Boolean_value fvf@89))))))
(assert (forall (($r $Ref)) (!
  (implies
    (and
      (and (<= 0 (invOf@87 $r)) (< (invOf@87 $r) $t@83))
      ($Set.in $r ($FVF.domain_Ref__Boolean_value fvf@89)))
    (=
      ($FVF.lookup_Ref__Boolean_value fvf@89 $r)
      ($FVF.lookup_Ref__Boolean_value $t@78 $r)))
  :pattern (($FVF.lookup_Ref__Boolean_value fvf@89 $r) (invOf@87 $r))
  :pattern (($FVF.lookup_Ref__Boolean_value $t@78 $r) (invOf@87 $r)))))
(assert (forall (($r $Ref)) (!
  (implies
    (and
      (<
        $Perm.No
        (-
          (ite
            (and
              (<= 0 (invOf@29 $r))
              (< (invOf@29 $r) ($Seq.length sys__result@25)))
            $Perm.Write
            $Perm.No)
          ($permsTaken4 $r)))
      ($Set.in $r ($FVF.domain_Ref__Boolean_value fvf@89)))
    (=
      ($FVF.lookup_Ref__Boolean_value fvf@89 $r)
      ($FVF.lookup_Ref__Boolean_value $t@27 $r)))
  :pattern (($FVF.lookup_Ref__Boolean_value fvf@89 $r) (invOf@29 $r))
  :pattern (($FVF.lookup_Ref__Boolean_value $t@27 $r) (invOf@29 $r)))))
(assert (forall ((k@88 Int)) (!
  (implies
    (and (<= 0 k@88) (< k@88 i@30))
    (not ($FVF.lookup_Ref__Boolean_value fvf@89 ($Seq.index $t@81 k@88))))
  :pattern (($Seq.index $t@81 k@88)))))
; [eval] !(i < max)
; [eval] i < max
(assert (not (< i@30 max@1)))
(set-option :timeout 0)
(check-sat)
; unknown
; [exec]
; sys__result := diz
; [exec]
; assert (sys__result != null) && acc(sys__result.Set__max, wildcard) && (sys__result.Set__max > 0) && acc(sys__result.Set__contents, wildcard) && (|sys__result.Set__contents| == sys__result.Set__max) && (forall k: Int :: (0 <= k) && (k < sys__result.Set__max) ==> acc(sys__result.Set__contents[k].Ref__Boolean_value, write)) && (sys__result.Set__max == max) && (forall k: Int :: (0 <= k) && (k < max) ==> !sys__result.Set__contents[k].Ref__Boolean_value)
; [eval] sys__result != null
(declare-const $k@90 $Perm)
(assert ($Perm.isValidVar $k@90))
(assert ($Perm.isReadVar $k@90 $Perm.Write))
(set-option :timeout 0)
(push) ; 5
(assert (not (or (= $k@90 $Perm.No) true)))
(check-sat)
; unsat
(pop) ; 5
; 0.00s
; (get-info :all-statistics)
(assert (< $k@90 (+ (- $Perm.Write $k@63) $k@84)))
; [eval] sys__result.Set__max > 0
(declare-const $k@91 $Perm)
(assert ($Perm.isValidVar $k@91))
(assert ($Perm.isReadVar $k@91 $Perm.Write))
(set-option :timeout 0)
(push) ; 5
(assert (not (or (= $k@91 $Perm.No) true)))
(check-sat)
; unsat
(pop) ; 5
; 0.00s
; (get-info :all-statistics)
(assert (< $k@91 (+ (- $Perm.Write $k@64) $k@85)))
; [eval] |sys__result.Set__contents| == sys__result.Set__max
; [eval] |sys__result.Set__contents|
(declare-const fvf@92 $FVF<Int>)
(declare-const fvf@93 $FVF<$Seq<$Ref>>)
(assert (= ($FVF.lookup_Set__max fvf@92 diz@20) $t@83))
(assert ($Set.equal ($FVF.domain_Set__max fvf@92) ($Set.singleton  diz@20)))
(assert ($Seq.equal ($FVF.lookup_Set__contents fvf@93 diz@20) $t@81))
(assert ($Set.equal ($FVF.domain_Set__contents fvf@93) ($Set.singleton  diz@20)))
(declare-const k@94 Int)
; [eval] (0 <= k) && (k < sys__result.Set__max)
; [eval] 0 <= k
(push) ; 5
(set-option :timeout 0)
(push) ; 6
(assert (not (not (<= 0 k@94))))
(check-sat)
; unknown
(pop) ; 6
; 0.00s
; (get-info :all-statistics)
(set-option :timeout 0)
(push) ; 6
(assert (not (<= 0 k@94)))
(check-sat)
; unknown
(pop) ; 6
; 0.00s
; (get-info :all-statistics)
(push) ; 6
; [then-branch 21] 0 <= k@94
(assert (<= 0 k@94))
; [eval] k < sys__result.Set__max
(set-option :timeout 0)
(push) ; 7
(assert (not (< $Perm.No (+ (- $Perm.Write $k@63) $k@84))))
(check-sat)
; unsat
(pop) ; 7
; 0.00s
; (get-info :all-statistics)
(declare-const fvf@95 $FVF<Int>)
(assert (implies
  (< $Perm.No (+ (- $Perm.Write $k@63) $k@84))
  (= ($FVF.lookup_Set__max fvf@95 diz@20) ($FVF.lookup_Set__max fvf@92 diz@20))))
(assert ($Set.equal ($FVF.domain_Set__max fvf@95) ($Set.singleton  diz@20)))
(pop) ; 6
(push) ; 6
; [else-branch 21] !0 <= k@94
(assert (not (<= 0 k@94)))
(pop) ; 6
(pop) ; 5
(assert ($Set.equal ($FVF.domain_Set__max fvf@95) ($Set.singleton  diz@20)))
(assert (implies
  (< $Perm.No (+ (- $Perm.Write $k@63) $k@84))
  (= ($FVF.lookup_Set__max fvf@95 diz@20) ($FVF.lookup_Set__max fvf@92 diz@20))))
(set-option :timeout 0)
(push) ; 5
(assert (not (not (and (<= 0 k@94) (< k@94 ($FVF.lookup_Set__max fvf@95 diz@20))))))
(check-sat)
; unknown
(pop) ; 5
; 0.00s
; (get-info :all-statistics)
(assert (and (<= 0 k@94) (< k@94 ($FVF.lookup_Set__max fvf@95 diz@20))))
; [eval] sys__result.Set__contents[k]
(set-option :timeout 0)
(push) ; 5
(assert (not (< $Perm.No (+ (- $Perm.Write $k@64) $k@85))))
(check-sat)
; unsat
(pop) ; 5
; 0.00s
; (get-info :all-statistics)
(declare-const fvf@96 $FVF<$Seq<$Ref>>)
(assert (implies
  (< $Perm.No (+ (- $Perm.Write $k@64) $k@85))
  ($Seq.equal
    ($FVF.lookup_Set__contents fvf@96 diz@20)
    ($FVF.lookup_Set__contents fvf@93 diz@20))))
(assert ($Set.equal ($FVF.domain_Set__contents fvf@96) ($Set.singleton  diz@20)))
(set-option :timeout 0)
(push) ; 5
(assert (not (forall (($x Int) ($y Int)) (!
  (implies
    (and
      (and (<= 0 $x) (< $x ($FVF.lookup_Set__max fvf@95 diz@20)))
      (and (<= 0 $y) (< $y ($FVF.lookup_Set__max fvf@95 diz@20)))
      (=
        ($Seq.index ($FVF.lookup_Set__contents fvf@96 diz@20) $x)
        ($Seq.index ($FVF.lookup_Set__contents fvf@96 diz@20) $y)))
    (= $x $y))
  :pattern (($Seq.index ($FVF.lookup_Set__contents fvf@96 diz@20) $x) ($Seq.index
    ($FVF.lookup_Set__contents fvf@96 diz@20)
    $y))))))
(check-sat)
; unsat
(pop) ; 5
; 0.00s
; (get-info :all-statistics)
(declare-fun invOf@97 ($Ref) Int)
(assert (forall (($r $Ref)) (!
  (implies
    (and
      (<= 0 (invOf@97 $r))
      (< (invOf@97 $r) ($FVF.lookup_Set__max fvf@95 diz@20)))
    (= ($Seq.index ($FVF.lookup_Set__contents fvf@96 diz@20) (invOf@97 $r)) $r))
  :pattern ((invOf@97 $r)))))
(assert (forall ((k@94 Int)) (!
  (implies
    (and (<= 0 k@94) (< k@94 ($FVF.lookup_Set__max fvf@95 diz@20)))
    (=
      (invOf@97 ($Seq.index ($FVF.lookup_Set__contents fvf@96 diz@20) k@94))
      k@94))
  :pattern (($Seq.index ($FVF.lookup_Set__contents fvf@96 diz@20) k@94)))))
(declare-const fvf@98 $FVF<Bool>)
; Precomputing split data for Lookup(Set__contents,fvf@96,diz@20)[k@94].Ref__Boolean_value # W
(define-fun $permsTaken5 (($r $Ref)) $Perm
  ($Perm.min
    (ite
      (and
        (<= 0 (invOf@97 $r))
        (< (invOf@97 $r) ($FVF.lookup_Set__max fvf@95 diz@20)))
      $Perm.Write
      $Perm.No)
    (ite
      (= $r ($Seq.index ($FVF.lookup_Set__contents fvf@96 diz@20) k@94))
      (ite
        (and (<= 0 (invOf@87 $r)) (< (invOf@87 $r) $t@83))
        $Perm.Write
        $Perm.No)
      $Perm.No)))
(define-fun $permsTaken6 (($r $Ref)) $Perm
  ($Perm.min
    (-
      (ite
        (and
          (<= 0 (invOf@97 $r))
          (< (invOf@97 $r) ($FVF.lookup_Set__max fvf@95 diz@20)))
        $Perm.Write
        $Perm.No)
      ($permsTaken5 $r))
    (ite
      (= $r ($Seq.index ($FVF.lookup_Set__contents fvf@96 diz@20) k@94))
      (-
        (ite
          (and
            (<= 0 (invOf@29 $r))
            (< (invOf@29 $r) ($Seq.length sys__result@25)))
          $Perm.Write
          $Perm.No)
        ($permsTaken4 $r))
      $Perm.No)))
; Done precomputing, updating quantified heap chunks
; Chunk depleted?
(set-option :timeout 500)
(push) ; 5
(assert (not (forall (($r $Ref)) (!
  (=
    (-
      (ite
        (and (<= 0 (invOf@87 $r)) (< (invOf@87 $r) $t@83))
        $Perm.Write
        $Perm.No)
      ($permsTaken5 $r))
    $Perm.No)
  ))))
(check-sat)
; unknown
(pop) ; 5
; 0.03s
; (get-info :all-statistics)
; Enough permissions taken?
(set-option :timeout 500)
(push) ; 5
(assert (not (=
  (-
    (ite
      (and
        (<=
          0
          (invOf@97 ($Seq.index ($FVF.lookup_Set__contents fvf@96 diz@20) k@94)))
        (<
          (invOf@97 ($Seq.index ($FVF.lookup_Set__contents fvf@96 diz@20) k@94))
          ($FVF.lookup_Set__max fvf@95 diz@20)))
      $Perm.Write
      $Perm.No)
    ($permsTaken5 ($Seq.index ($FVF.lookup_Set__contents fvf@96 diz@20) k@94)))
  $Perm.No)))
(check-sat)
; unsat
(pop) ; 5
; 0.00s
; (get-info :all-statistics)
; Final check that enough permissions have been taken
; Done splitting
(assert (forall (($r $Ref)) (!
  (implies
    (and
      (<
        $Perm.No
        (-
          (ite
            (and
              (<= 0 (invOf@29 $r))
              (< (invOf@29 $r) ($Seq.length sys__result@25)))
            $Perm.Write
            $Perm.No)
          ($permsTaken4 $r)))
      ($Set.in $r ($FVF.domain_Ref__Boolean_value fvf@98)))
    (=
      ($FVF.lookup_Ref__Boolean_value fvf@98 $r)
      ($FVF.lookup_Ref__Boolean_value $t@27 $r)))
  :pattern (($FVF.lookup_Ref__Boolean_value fvf@98 $r) (invOf@29 $r))
  :pattern (($FVF.lookup_Ref__Boolean_value $t@27 $r) (invOf@29 $r)))))
(assert (forall (($r $Ref)) (!
  (implies
    (and
      (and (<= 0 (invOf@87 $r)) (< (invOf@87 $r) $t@83))
      ($Set.in $r ($FVF.domain_Ref__Boolean_value fvf@98)))
    (=
      ($FVF.lookup_Ref__Boolean_value fvf@98 $r)
      ($FVF.lookup_Ref__Boolean_value $t@78 $r)))
  :pattern (($FVF.lookup_Ref__Boolean_value fvf@98 $r) (invOf@87 $r))
  :pattern (($FVF.lookup_Ref__Boolean_value $t@78 $r) (invOf@87 $r)))))
(assert (forall (($r $Ref)) (!
  (iff
    ($Set.in $r ($FVF.domain_Ref__Boolean_value fvf@98))
    (and
      (<= 0 (invOf@97 $r))
      (< (invOf@97 $r) ($FVF.lookup_Set__max fvf@95 diz@20))))
  :pattern (($Set.in $r ($FVF.domain_Ref__Boolean_value fvf@98))))))
; [eval] sys__result.Set__max == max
; [eval] (forall k: Int :: (0 <= k) && (k < max) ==> !sys__result.Set__contents[k].Ref__Boolean_value)
(declare-const k@99 Int)
(push) ; 5
; [eval] (0 <= k) && (k < max) ==> !sys__result.Set__contents[k].Ref__Boolean_value
; [eval] (0 <= k) && (k < max)
; [eval] 0 <= k
(push) ; 6
(set-option :timeout 0)
(push) ; 7
(assert (not (not (<= 0 k@99))))
(check-sat)
; unknown
(pop) ; 7
; 0.00s
; (get-info :all-statistics)
(set-option :timeout 0)
(push) ; 7
(assert (not (<= 0 k@99)))
(check-sat)
; unknown
(pop) ; 7
; 0.00s
; (get-info :all-statistics)
(push) ; 7
; [then-branch 22] 0 <= k@99
(assert (<= 0 k@99))
; [eval] k < max
(pop) ; 7
(push) ; 7
; [else-branch 22] !0 <= k@99
(assert (not (<= 0 k@99)))
(pop) ; 7
(pop) ; 6
(push) ; 6
(set-option :timeout 0)
(push) ; 7
(assert (not (not (and (<= 0 k@99) (< k@99 max@1)))))
(check-sat)
; unknown
(pop) ; 7
; 0.00s
; (get-info :all-statistics)
(set-option :timeout 0)
(push) ; 7
(assert (not (and (<= 0 k@99) (< k@99 max@1))))
(check-sat)
; unknown
(pop) ; 7
; 0.00s
; (get-info :all-statistics)
(push) ; 7
; [then-branch 23] 0 <= k@99 && k@99 < max@1
(assert (and (<= 0 k@99) (< k@99 max@1)))
; [eval] !sys__result.Set__contents[k].Ref__Boolean_value
; [eval] sys__result.Set__contents[k]
(set-option :timeout 0)
(push) ; 8
(assert (not (not (= ($Seq.index $t@81 k@99) $Ref.null))))
(check-sat)
; unsat
(pop) ; 8
; 0.00s
; (get-info :all-statistics)
(set-option :timeout 0)
(push) ; 8
(assert (not (<
  $Perm.No
  (+
    (-
      (ite
        (and
          (<= 0 (invOf@29 ($Seq.index $t@81 k@99)))
          (< (invOf@29 ($Seq.index $t@81 k@99)) ($Seq.length sys__result@25)))
        $Perm.Write
        $Perm.No)
      ($permsTaken4 ($Seq.index $t@81 k@99)))
    (ite
      (and
        (<= 0 (invOf@87 ($Seq.index $t@81 k@99)))
        (< (invOf@87 ($Seq.index $t@81 k@99)) $t@83))
      $Perm.Write
      $Perm.No)))))
(check-sat)
; unsat
(pop) ; 8
; 0.00s
; (get-info :all-statistics)
(declare-const fvf@100 $FVF<Bool>)
(assert (forall (($r $Ref)) (!
  (implies
    (and
      (<
        $Perm.No
        (-
          (ite
            (and
              (<= 0 (invOf@29 $r))
              (< (invOf@29 $r) ($Seq.length sys__result@25)))
            $Perm.Write
            $Perm.No)
          ($permsTaken4 $r)))
      ($Set.in $r ($FVF.domain_Ref__Boolean_value fvf@100)))
    (=
      ($FVF.lookup_Ref__Boolean_value fvf@100 $r)
      ($FVF.lookup_Ref__Boolean_value $t@27 $r)))
  :pattern (($FVF.lookup_Ref__Boolean_value fvf@100 $r) (invOf@29 $r))
  :pattern (($FVF.lookup_Ref__Boolean_value $t@27 $r) (invOf@29 $r)))))
(assert (forall (($r $Ref)) (!
  (implies
    (and
      (and (<= 0 (invOf@87 $r)) (< (invOf@87 $r) $t@83))
      ($Set.in $r ($FVF.domain_Ref__Boolean_value fvf@100)))
    (=
      ($FVF.lookup_Ref__Boolean_value fvf@100 $r)
      ($FVF.lookup_Ref__Boolean_value $t@78 $r)))
  :pattern (($FVF.lookup_Ref__Boolean_value fvf@100 $r) (invOf@87 $r))
  :pattern (($FVF.lookup_Ref__Boolean_value $t@78 $r) (invOf@87 $r)))))
(assert (forall ((k@99 Int)) (!
  (iff
    ($Set.in ($Seq.index $t@81 k@99) ($FVF.domain_Ref__Boolean_value fvf@100))
    (and (<= 0 k@99) (< k@99 max@1)))
  :pattern (($Set.in
    ($Seq.index $t@81 k@99)
    ($FVF.domain_Ref__Boolean_value fvf@100))))))
(pop) ; 7
(push) ; 7
; [else-branch 23] !0 <= k@99 && k@99 < max@1
(assert (not (and (<= 0 k@99) (< k@99 max@1))))
(pop) ; 7
(pop) ; 6
(assert (forall ((k@99 Int)) (!
  (iff
    ($Set.in ($Seq.index $t@81 k@99) ($FVF.domain_Ref__Boolean_value fvf@100))
    (and (<= 0 k@99) (< k@99 max@1)))
  :pattern (($Set.in
    ($Seq.index $t@81 k@99)
    ($FVF.domain_Ref__Boolean_value fvf@100))))))
(assert (forall (($r $Ref)) (!
  (implies
    (and
      (and (<= 0 (invOf@87 $r)) (< (invOf@87 $r) $t@83))
      ($Set.in $r ($FVF.domain_Ref__Boolean_value fvf@100)))
    (=
      ($FVF.lookup_Ref__Boolean_value fvf@100 $r)
      ($FVF.lookup_Ref__Boolean_value $t@78 $r)))
  :pattern (($FVF.lookup_Ref__Boolean_value fvf@100 $r) (invOf@87 $r))
  :pattern (($FVF.lookup_Ref__Boolean_value $t@78 $r) (invOf@87 $r)))))
(assert (forall (($r $Ref)) (!
  (implies
    (and
      (<
        $Perm.No
        (-
          (ite
            (and
              (<= 0 (invOf@29 $r))
              (< (invOf@29 $r) ($Seq.length sys__result@25)))
            $Perm.Write
            $Perm.No)
          ($permsTaken4 $r)))
      ($Set.in $r ($FVF.domain_Ref__Boolean_value fvf@100)))
    (=
      ($FVF.lookup_Ref__Boolean_value fvf@100 $r)
      ($FVF.lookup_Ref__Boolean_value $t@27 $r)))
  :pattern (($FVF.lookup_Ref__Boolean_value fvf@100 $r) (invOf@29 $r))
  :pattern (($FVF.lookup_Ref__Boolean_value $t@27 $r) (invOf@29 $r)))))
(pop) ; 5
(assert (forall ((k@99 Int)) (!
  (iff
    ($Set.in ($Seq.index $t@81 k@99) ($FVF.domain_Ref__Boolean_value fvf@100))
    (and (<= 0 k@99) (< k@99 max@1)))
  :pattern (($Set.in
    ($Seq.index $t@81 k@99)
    ($FVF.domain_Ref__Boolean_value fvf@100))))))
(assert (forall (($r $Ref)) (!
  (implies
    (and
      (and (<= 0 (invOf@87 $r)) (< (invOf@87 $r) $t@83))
      ($Set.in $r ($FVF.domain_Ref__Boolean_value fvf@100)))
    (=
      ($FVF.lookup_Ref__Boolean_value fvf@100 $r)
      ($FVF.lookup_Ref__Boolean_value $t@78 $r)))
  :pattern (($FVF.lookup_Ref__Boolean_value fvf@100 $r) (invOf@87 $r))
  :pattern (($FVF.lookup_Ref__Boolean_value $t@78 $r) (invOf@87 $r)))))
(assert (forall (($r $Ref)) (!
  (implies
    (and
      (<
        $Perm.No
        (-
          (ite
            (and
              (<= 0 (invOf@29 $r))
              (< (invOf@29 $r) ($Seq.length sys__result@25)))
            $Perm.Write
            $Perm.No)
          ($permsTaken4 $r)))
      ($Set.in $r ($FVF.domain_Ref__Boolean_value fvf@100)))
    (=
      ($FVF.lookup_Ref__Boolean_value fvf@100 $r)
      ($FVF.lookup_Ref__Boolean_value $t@27 $r)))
  :pattern (($FVF.lookup_Ref__Boolean_value fvf@100 $r) (invOf@29 $r))
  :pattern (($FVF.lookup_Ref__Boolean_value $t@27 $r) (invOf@29 $r)))))
(set-option :timeout 0)
(push) ; 5
(assert (not (forall ((k@99 Int)) (!
  (implies
    (and (<= 0 k@99) (< k@99 max@1))
    (not ($FVF.lookup_Ref__Boolean_value fvf@100 ($Seq.index $t@81 k@99))))
  :pattern (($Seq.index $t@81 k@99))))))
(check-sat)
; unsat
(pop) ; 5
; 0.00s
; (get-info :all-statistics)
(assert (forall ((k@99 Int)) (!
  (implies
    (and (<= 0 k@99) (< k@99 max@1))
    (not ($FVF.lookup_Ref__Boolean_value fvf@100 ($Seq.index $t@81 k@99))))
  :pattern (($Seq.index $t@81 k@99)))))
; [exec]
; inhale false
(pop) ; 4
(pop) ; 3
(pop) ; 2
; ---------- Set__intersection ----------
(declare-const diz@101 $Ref)
(declare-const x@102 $Ref)
(declare-const i@103 Int)
(declare-const j@104 Int)
(declare-const __flatten_8@105 $Ref)
(declare-const __flatten_9@106 Bool)
(declare-const __flatten_10@107 $Ref)
(declare-const __flatten_11@108 $Ref)
(declare-const __flatten_12@109 $Ref)
(declare-const __flatten_13@110 Bool)
(declare-const __flatten_14@111 $Ref)
(declare-const __flatten_15@112 $Ref)
(declare-const __flatten_16@113 $Ref)
(declare-const __flatten_17@114 Bool)
(push) ; 2
; [eval] diz != null
(assert (not (= diz@101 $Ref.null)))
(declare-const $k@115 $Perm)
(assert ($Perm.isValidVar $k@115))
(assert ($Perm.isReadVar $k@115 $Perm.Write))
(declare-const $t@116 Int)
; [eval] diz.Set__max > 0
(set-option :timeout 0)
(push) ; 3
(assert (not (not (= $k@115 $Perm.No))))
(check-sat)
; unsat
(pop) ; 3
; 0.00s
; (get-info :all-statistics)
(assert (not (= $k@115 $Perm.No)))
(assert (> $t@116 0))
(declare-const $k@117 $Perm)
(assert ($Perm.isValidVar $k@117))
(assert ($Perm.isReadVar $k@117 $Perm.Write))
(declare-const $t@118 $Seq<$Ref>)
; [eval] |diz.Set__contents| == diz.Set__max
; [eval] |diz.Set__contents|
(set-option :timeout 0)
(push) ; 3
(assert (not (not (= $k@117 $Perm.No))))
(check-sat)
; unsat
(pop) ; 3
; 0.00s
; (get-info :all-statistics)
(assert (not (= $k@117 $Perm.No)))
(assert (= ($Seq.length $t@118) $t@116))
(declare-const k@119 Int)
(push) ; 3
; [eval] (0 <= k) && (k < diz.Set__max)
; [eval] 0 <= k
(push) ; 4
(set-option :timeout 0)
(push) ; 5
(assert (not (not (<= 0 k@119))))
(check-sat)
; unknown
(pop) ; 5
; 0.00s
; (get-info :all-statistics)
(set-option :timeout 0)
(push) ; 5
(assert (not (<= 0 k@119)))
(check-sat)
; unknown
(pop) ; 5
; 0.00s
; (get-info :all-statistics)
(push) ; 5
; [then-branch 24] 0 <= k@119
(assert (<= 0 k@119))
; [eval] k < diz.Set__max
(pop) ; 5
(push) ; 5
; [else-branch 24] !0 <= k@119
(assert (not (<= 0 k@119)))
(pop) ; 5
(pop) ; 4
(assert (and (<= 0 k@119) (< k@119 $t@116)))
; [eval] diz.Set__contents[k]
(pop) ; 3
(declare-const $t@120 $FVF<Bool>)
(declare-fun invOf@121 ($Ref) Int)
(assert (forall (($r $Ref)) (!
  (implies
    (and (<= 0 (invOf@121 $r)) (< (invOf@121 $r) $t@116))
    (= ($Seq.index $t@118 (invOf@121 $r)) $r))
  :pattern ((invOf@121 $r)))))
(assert (forall ((k@119 Int)) (!
  (implies
    (and (<= 0 k@119) (< k@119 $t@116))
    (= (invOf@121 ($Seq.index $t@118 k@119)) k@119))
  :pattern (($Seq.index $t@118 k@119)))))
(assert (forall ((k@119 Int)) (!
  (iff
    ($Set.in ($Seq.index $t@118 k@119) ($FVF.domain_Ref__Boolean_value $t@120))
    (and (<= 0 k@119) (< k@119 $t@116)))
  :pattern (($Set.in
    ($Seq.index $t@118 k@119)
    ($FVF.domain_Ref__Boolean_value $t@120))))))
(assert (forall ((k@119 Int)) (!
  (implies
    (and (<= 0 k@119) (< k@119 $t@116))
    (not (= ($Seq.index $t@118 k@119) $Ref.null)))
  :pattern (($Seq.index $t@118 k@119)))))
; [eval] x != null
(assert (not (= x@102 $Ref.null)))
(declare-const $k@122 $Perm)
(assert ($Perm.isValidVar $k@122))
(assert ($Perm.isReadVar $k@122 $Perm.Write))
(declare-const $t@123 Int)
(set-option :timeout 0)
(push) ; 3
(assert (not (= diz@101 x@102)))
(check-sat)
; unknown
(pop) ; 3
; 0.00s
; (get-info :all-statistics)
; [eval] x.Set__max > 0
(set-option :timeout 0)
(push) ; 3
(assert (not (not (= $k@122 $Perm.No))))
(check-sat)
; unsat
(pop) ; 3
; 0.00s
; (get-info :all-statistics)
(assert (not (= $k@122 $Perm.No)))
(assert (> $t@123 0))
(declare-const $k@124 $Perm)
(assert ($Perm.isValidVar $k@124))
(assert ($Perm.isReadVar $k@124 $Perm.Write))
(declare-const $t@125 $Seq<$Ref>)
(set-option :timeout 0)
(push) ; 3
(assert (not (= diz@101 x@102)))
(check-sat)
; unknown
(pop) ; 3
; 0.00s
; (get-info :all-statistics)
(declare-const k@126 Int)
(push) ; 3
; [eval] (0 <= k) && (k < x.Set__max)
; [eval] 0 <= k
(push) ; 4
(set-option :timeout 0)
(push) ; 5
(assert (not (not (<= 0 k@126))))
(check-sat)
; unknown
(pop) ; 5
; 0.00s
; (get-info :all-statistics)
(set-option :timeout 0)
(push) ; 5
(assert (not (<= 0 k@126)))
(check-sat)
; unknown
(pop) ; 5
; 0.00s
; (get-info :all-statistics)
(push) ; 5
; [then-branch 25] 0 <= k@126
(assert (<= 0 k@126))
; [eval] k < x.Set__max
(pop) ; 5
(push) ; 5
; [else-branch 25] !0 <= k@126
(assert (not (<= 0 k@126)))
(pop) ; 5
(pop) ; 4
(assert (and (<= 0 k@126) (< k@126 $t@123)))
; [eval] x.Set__contents[k]
(set-option :timeout 0)
(push) ; 4
(assert (not (not (= $k@124 $Perm.No))))
(check-sat)
; unsat
(pop) ; 4
; 0.00s
; (get-info :all-statistics)
(assert (not (= $k@124 $Perm.No)))
(declare-const $k@127 $Perm)
(assert ($Perm.isValidVar $k@127))
(assert ($Perm.isReadVar $k@127 $Perm.Write))
(pop) ; 3
(assert (not (= $k@124 $Perm.No)))
(assert ($Perm.isValidVar $k@127))
(assert ($Perm.isReadVar $k@127 $Perm.Write))
(declare-const $t@128 $FVF<Bool>)
(declare-fun invOf@129 ($Ref) Int)
(assert (forall (($r $Ref)) (!
  (implies
    (and (<= 0 (invOf@129 $r)) (< (invOf@129 $r) $t@123))
    (= ($Seq.index $t@125 (invOf@129 $r)) $r))
  :pattern ((invOf@129 $r)))))
(assert (forall ((k@126 Int)) (!
  (implies
    (and (<= 0 k@126) (< k@126 $t@123))
    (= (invOf@129 ($Seq.index $t@125 k@126)) k@126))
  :pattern (($Seq.index $t@125 k@126)))))
(assert (forall ((k@126 Int)) (!
  (iff
    ($Set.in ($Seq.index $t@125 k@126) ($FVF.domain_Ref__Boolean_value $t@128))
    (and (<= 0 k@126) (< k@126 $t@123)))
  :pattern (($Set.in
    ($Seq.index $t@125 k@126)
    ($FVF.domain_Ref__Boolean_value $t@128))))))
(assert (forall ((k@126 Int)) (!
  (implies
    (and (and (<= 0 k@126) (< k@126 $t@123)) (< $Perm.No $k@127))
    (not (= ($Seq.index $t@125 k@126) $Ref.null)))
  :pattern (($Seq.index $t@125 k@126)))))
(assert (< $Perm.No $k@127))
(push) ; 3
(declare-const $k@130 $Perm)
(assert ($Perm.isValidVar $k@130))
(assert ($Perm.isReadVar $k@130 $Perm.Write))
(declare-const $t@131 Int)
; [eval] diz.Set__max > 0
(set-option :timeout 0)
(push) ; 4
(assert (not (not (= $k@130 $Perm.No))))
(check-sat)
; unsat
(pop) ; 4
; 0.00s
; (get-info :all-statistics)
(assert (not (= $k@130 $Perm.No)))
(assert (> $t@131 0))
(declare-const $k@132 $Perm)
(assert ($Perm.isValidVar $k@132))
(assert ($Perm.isReadVar $k@132 $Perm.Write))
(declare-const $t@133 $Seq<$Ref>)
; [eval] |diz.Set__contents| == diz.Set__max
; [eval] |diz.Set__contents|
(set-option :timeout 0)
(push) ; 4
(assert (not (not (= $k@132 $Perm.No))))
(check-sat)
; unsat
(pop) ; 4
; 0.00s
; (get-info :all-statistics)
(assert (not (= $k@132 $Perm.No)))
(assert (= ($Seq.length $t@133) $t@131))
(declare-const k@134 Int)
(push) ; 4
; [eval] (0 <= k) && (k < diz.Set__max)
; [eval] 0 <= k
(push) ; 5
(set-option :timeout 0)
(push) ; 6
(assert (not (not (<= 0 k@134))))
(check-sat)
; unknown
(pop) ; 6
; 0.00s
; (get-info :all-statistics)
(set-option :timeout 0)
(push) ; 6
(assert (not (<= 0 k@134)))
(check-sat)
; unknown
(pop) ; 6
; 0.00s
; (get-info :all-statistics)
(push) ; 6
; [then-branch 26] 0 <= k@134
(assert (<= 0 k@134))
; [eval] k < diz.Set__max
(pop) ; 6
(push) ; 6
; [else-branch 26] !0 <= k@134
(assert (not (<= 0 k@134)))
(pop) ; 6
(pop) ; 5
(assert (and (<= 0 k@134) (< k@134 $t@131)))
; [eval] diz.Set__contents[k]
(pop) ; 4
(declare-const $t@135 $FVF<Bool>)
(declare-fun invOf@136 ($Ref) Int)
(assert (forall (($r $Ref)) (!
  (implies
    (and (<= 0 (invOf@136 $r)) (< (invOf@136 $r) $t@131))
    (= ($Seq.index $t@133 (invOf@136 $r)) $r))
  :pattern ((invOf@136 $r)))))
(assert (forall ((k@134 Int)) (!
  (implies
    (and (<= 0 k@134) (< k@134 $t@131))
    (= (invOf@136 ($Seq.index $t@133 k@134)) k@134))
  :pattern (($Seq.index $t@133 k@134)))))
(assert (forall ((k@134 Int)) (!
  (iff
    ($Set.in ($Seq.index $t@133 k@134) ($FVF.domain_Ref__Boolean_value $t@135))
    (and (<= 0 k@134) (< k@134 $t@131)))
  :pattern (($Set.in
    ($Seq.index $t@133 k@134)
    ($FVF.domain_Ref__Boolean_value $t@135))))))
(assert (forall ((k@134 Int)) (!
  (implies
    (and (<= 0 k@134) (< k@134 $t@131))
    (not (= ($Seq.index $t@133 k@134) $Ref.null)))
  :pattern (($Seq.index $t@133 k@134)))))
(pop) ; 3
(push) ; 3
; [exec]
; i := 0
; [exec]
; j := 0
; [eval] diz.Set__max <= x.Set__max
(set-option :timeout 0)
(push) ; 4
(assert (not (not (<= $t@116 $t@123))))
(check-sat)
; unknown
(pop) ; 4
; 0.00s
; (get-info :all-statistics)
(set-option :timeout 0)
(push) ; 4
(assert (not (<= $t@116 $t@123)))
(check-sat)
; unknown
(pop) ; 4
; 0.00s
; (get-info :all-statistics)
(push) ; 4
; [then-branch 27] $t@116 <= $t@123
(assert (<= $t@116 $t@123))
; loop at <no position>
(declare-const i@137 Int)
(declare-const __flatten_9@138 Bool)
(declare-const __flatten_11@139 $Ref)
(declare-const __flatten_10@140 $Ref)
(declare-const __flatten_8@141 $Ref)
(push) ; 5
; Verify loop body
(declare-const $t@142 $Snap)
(declare-const $t@143 $Snap)
(assert (= $t@142 ($Snap.combine $t@143 $Snap.unit)))
(declare-const $t@144 $Snap)
(assert (= $t@143 ($Snap.combine $t@144 $Snap.unit)))
(declare-const $t@145 $Snap)
(assert (= $t@144 ($Snap.combine $t@145 $Snap.unit)))
(declare-const $t@146 $Snap)
(declare-const $t@147 $FVF<Bool>)
(assert (= $t@145 ($Snap.combine $t@146 ($SortWrappers.$FVF<Bool>To$Snap $t@147))))
(declare-const $t@148 $Snap)
(assert (= $t@146 ($Snap.combine $t@148 $Snap.unit)))
(declare-const $t@149 $Snap)
(declare-const $t@150 $Seq<$Ref>)
(assert (= $t@148 ($Snap.combine $t@149 ($SortWrappers.$Seq<$Ref>To$Snap $t@150))))
(declare-const $t@151 $Snap)
(assert (= $t@149 ($Snap.combine $t@151 $Snap.unit)))
(declare-const $t@152 $Snap)
(declare-const $t@153 Int)
(assert (= $t@151 ($Snap.combine $t@152 ($SortWrappers.IntTo$Snap $t@153))))
(declare-const $t@154 $Snap)
(assert (= $t@152 ($Snap.combine $t@154 $Snap.unit)))
(declare-const $t@155 $Snap)
(declare-const $t@156 $FVF<Bool>)
(assert (= $t@154 ($Snap.combine $t@155 ($SortWrappers.$FVF<Bool>To$Snap $t@156))))
(declare-const $t@157 $Snap)
(assert (= $t@155 ($Snap.combine $t@157 $Snap.unit)))
(declare-const $t@158 Int)
(declare-const $t@159 $Seq<$Ref>)
(assert (=
  $t@157
  ($Snap.combine
    ($SortWrappers.IntTo$Snap $t@158)
    ($SortWrappers.$Seq<$Ref>To$Snap $t@159))))
(declare-const $t@160 Int)
(assert (=
  ($SortWrappers.IntTo$Snap $t@158)
  ($Snap.combine ($SortWrappers.IntTo$Snap $t@160) $Snap.unit)))
(declare-const $k@161 $Perm)
(assert ($Perm.isValidVar $k@161))
(assert ($Perm.isReadVar $k@161 $Perm.Write))
; [eval] diz.Set__max > 0
(set-option :timeout 0)
(push) ; 6
(assert (not (not (= $k@161 $Perm.No))))
(check-sat)
; unsat
(pop) ; 6
; 0.00s
; (get-info :all-statistics)
(assert (not (= $k@161 $Perm.No)))
(assert (> $t@160 0))
(declare-const $k@162 $Perm)
(assert ($Perm.isValidVar $k@162))
(assert ($Perm.isReadVar $k@162 $Perm.Write))
; [eval] |diz.Set__contents| == diz.Set__max
; [eval] |diz.Set__contents|
(set-option :timeout 0)
(push) ; 6
(assert (not (not (= $k@162 $Perm.No))))
(check-sat)
; unsat
(pop) ; 6
; 0.00s
; (get-info :all-statistics)
(assert (not (= $k@162 $Perm.No)))
(assert (= ($Seq.length $t@159) $t@160))
(declare-const k@163 Int)
(push) ; 6
; [eval] (0 <= k) && (k < diz.Set__max)
; [eval] 0 <= k
(push) ; 7
(set-option :timeout 0)
(push) ; 8
(assert (not (not (<= 0 k@163))))
(check-sat)
; unknown
(pop) ; 8
; 0.00s
; (get-info :all-statistics)
(set-option :timeout 0)
(push) ; 8
(assert (not (<= 0 k@163)))
(check-sat)
; unknown
(pop) ; 8
; 0.00s
; (get-info :all-statistics)
(push) ; 8
; [then-branch 28] 0 <= k@163
(assert (<= 0 k@163))
; [eval] k < diz.Set__max
(pop) ; 8
(push) ; 8
; [else-branch 28] !0 <= k@163
(assert (not (<= 0 k@163)))
(pop) ; 8
(pop) ; 7
(assert (and (<= 0 k@163) (< k@163 $t@160)))
; [eval] diz.Set__contents[k]
(pop) ; 6
(declare-fun invOf@164 ($Ref) Int)
(assert (forall (($r $Ref)) (!
  (implies
    (and (<= 0 (invOf@164 $r)) (< (invOf@164 $r) $t@160))
    (= ($Seq.index $t@159 (invOf@164 $r)) $r))
  :pattern ((invOf@164 $r)))))
(assert (forall ((k@163 Int)) (!
  (implies
    (and (<= 0 k@163) (< k@163 $t@160))
    (= (invOf@164 ($Seq.index $t@159 k@163)) k@163))
  :pattern (($Seq.index $t@159 k@163)))))
(assert (forall ((k@163 Int)) (!
  (iff
    ($Set.in ($Seq.index $t@159 k@163) ($FVF.domain_Ref__Boolean_value $t@156))
    (and (<= 0 k@163) (< k@163 $t@160)))
  :pattern (($Set.in
    ($Seq.index $t@159 k@163)
    ($FVF.domain_Ref__Boolean_value $t@156))))))
(assert (forall ((k@163 Int)) (!
  (implies
    (and (<= 0 k@163) (< k@163 $t@160))
    (not (= ($Seq.index $t@159 k@163) $Ref.null)))
  :pattern (($Seq.index $t@159 k@163)))))
; [eval] x != null
(declare-const $k@165 $Perm)
(assert ($Perm.isValidVar $k@165))
(assert ($Perm.isReadVar $k@165 $Perm.Write))
(set-option :timeout 0)
(push) ; 6
(assert (not (= diz@101 x@102)))
(check-sat)
; unknown
(pop) ; 6
; 0.00s
; (get-info :all-statistics)
; [eval] x.Set__max > 0
(set-option :timeout 0)
(push) ; 6
(assert (not (not (= $k@165 $Perm.No))))
(check-sat)
; unsat
(pop) ; 6
; 0.00s
; (get-info :all-statistics)
(assert (not (= $k@165 $Perm.No)))
(assert (> $t@153 0))
(declare-const $k@166 $Perm)
(assert ($Perm.isValidVar $k@166))
(assert ($Perm.isReadVar $k@166 $Perm.Write))
(set-option :timeout 0)
(push) ; 6
(assert (not (= diz@101 x@102)))
(check-sat)
; unknown
(pop) ; 6
; 0.00s
; (get-info :all-statistics)
; [eval] x.Set__max >= diz.Set__max
(assert (>= $t@153 $t@160))
(declare-const k@167 Int)
(push) ; 6
; [eval] (0 <= k) && (k < x.Set__max)
; [eval] 0 <= k
(push) ; 7
(set-option :timeout 0)
(push) ; 8
(assert (not (not (<= 0 k@167))))
(check-sat)
; unknown
(pop) ; 8
; 0.00s
; (get-info :all-statistics)
(set-option :timeout 0)
(push) ; 8
(assert (not (<= 0 k@167)))
(check-sat)
; unknown
(pop) ; 8
; 0.00s
; (get-info :all-statistics)
(push) ; 8
; [then-branch 29] 0 <= k@167
(assert (<= 0 k@167))
; [eval] k < x.Set__max
(pop) ; 8
(push) ; 8
; [else-branch 29] !0 <= k@167
(assert (not (<= 0 k@167)))
(pop) ; 8
(pop) ; 7
(assert (and (<= 0 k@167) (< k@167 $t@153)))
; [eval] x.Set__contents[k]
(set-option :timeout 0)
(push) ; 7
(assert (not (not (= $k@166 $Perm.No))))
(check-sat)
; unsat
(pop) ; 7
; 0.00s
; (get-info :all-statistics)
(assert (not (= $k@166 $Perm.No)))
(declare-const $k@168 $Perm)
(assert ($Perm.isValidVar $k@168))
(assert ($Perm.isReadVar $k@168 $Perm.Write))
(pop) ; 6
(assert (not (= $k@166 $Perm.No)))
(assert ($Perm.isValidVar $k@168))
(assert ($Perm.isReadVar $k@168 $Perm.Write))
(declare-fun invOf@169 ($Ref) Int)
(assert (forall (($r $Ref)) (!
  (implies
    (and (<= 0 (invOf@169 $r)) (< (invOf@169 $r) $t@153))
    (= ($Seq.index $t@150 (invOf@169 $r)) $r))
  :pattern ((invOf@169 $r)))))
(assert (forall ((k@167 Int)) (!
  (implies
    (and (<= 0 k@167) (< k@167 $t@153))
    (= (invOf@169 ($Seq.index $t@150 k@167)) k@167))
  :pattern (($Seq.index $t@150 k@167)))))
(assert (forall ((k@167 Int)) (!
  (iff
    ($Set.in ($Seq.index $t@150 k@167) ($FVF.domain_Ref__Boolean_value $t@147))
    (and (<= 0 k@167) (< k@167 $t@153)))
  :pattern (($Set.in
    ($Seq.index $t@150 k@167)
    ($FVF.domain_Ref__Boolean_value $t@147))))))
(assert (forall ((k@167 Int)) (!
  (implies
    (and (and (<= 0 k@167) (< k@167 $t@153)) (< $Perm.No $k@168))
    (not (= ($Seq.index $t@150 k@167) $Ref.null)))
  :pattern (($Seq.index $t@150 k@167)))))
(assert (< $Perm.No $k@168))
; [eval] (0 <= i) && (i <= diz.Set__max)
; [eval] 0 <= i
(push) ; 6
(set-option :timeout 0)
(push) ; 7
(assert (not (not (<= 0 i@137))))
(check-sat)
; unknown
(pop) ; 7
; 0.00s
; (get-info :all-statistics)
(set-option :timeout 0)
(push) ; 7
(assert (not (<= 0 i@137)))
(check-sat)
; unknown
(pop) ; 7
; 0.00s
; (get-info :all-statistics)
(push) ; 7
; [then-branch 30] 0 <= i@137
(assert (<= 0 i@137))
; [eval] i <= diz.Set__max
(pop) ; 7
(push) ; 7
; [else-branch 30] !0 <= i@137
(assert (not (<= 0 i@137)))
(pop) ; 7
(pop) ; 6
(assert (and (<= 0 i@137) (<= i@137 $t@160)))
; [eval] (forall k: Int :: (0 <= k) && (k < i) ==> (diz.Set__contents[k].Ref__Boolean_value == diz.Set__contents[k].Ref__Boolean_value && x.Set__contents[k].Ref__Boolean_value))
(declare-const k@170 Int)
(push) ; 6
; [eval] (0 <= k) && (k < i) ==> (diz.Set__contents[k].Ref__Boolean_value == diz.Set__contents[k].Ref__Boolean_value && x.Set__contents[k].Ref__Boolean_value)
; [eval] (0 <= k) && (k < i)
; [eval] 0 <= k
(push) ; 7
(set-option :timeout 0)
(push) ; 8
(assert (not (not (<= 0 k@170))))
(check-sat)
; unknown
(pop) ; 8
; 0.00s
; (get-info :all-statistics)
(set-option :timeout 0)
(push) ; 8
(assert (not (<= 0 k@170)))
(check-sat)
; unknown
(pop) ; 8
; 0.00s
; (get-info :all-statistics)
(push) ; 8
; [then-branch 31] 0 <= k@170
(assert (<= 0 k@170))
; [eval] k < i
(pop) ; 8
(push) ; 8
; [else-branch 31] !0 <= k@170
(assert (not (<= 0 k@170)))
(pop) ; 8
(pop) ; 7
(push) ; 7
(set-option :timeout 0)
(push) ; 8
(assert (not (not (and (<= 0 k@170) (< k@170 i@137)))))
(check-sat)
; unknown
(pop) ; 8
; 0.00s
; (get-info :all-statistics)
(set-option :timeout 0)
(push) ; 8
(assert (not (and (<= 0 k@170) (< k@170 i@137))))
(check-sat)
; unknown
(pop) ; 8
; 0.00s
; (get-info :all-statistics)
(push) ; 8
; [then-branch 32] 0 <= k@170 && k@170 < i@137
(assert (and (<= 0 k@170) (< k@170 i@137)))
; [eval] diz.Set__contents[k].Ref__Boolean_value == diz.Set__contents[k].Ref__Boolean_value && x.Set__contents[k].Ref__Boolean_value
; [eval] diz.Set__contents[k]
(set-option :timeout 0)
(push) ; 9
(assert (not (not (= ($Seq.index $t@159 k@170) $Ref.null))))
(check-sat)
; unsat
(pop) ; 9
; 0.00s
; (get-info :all-statistics)
(set-option :timeout 0)
(push) ; 9
(assert (not (<
  $Perm.No
  (+
    (ite
      (and
        (<= 0 (invOf@164 ($Seq.index $t@159 k@170)))
        (< (invOf@164 ($Seq.index $t@159 k@170)) $t@160))
      $Perm.Write
      $Perm.No)
    (ite
      (and
        (<= 0 (invOf@169 ($Seq.index $t@159 k@170)))
        (< (invOf@169 ($Seq.index $t@159 k@170)) $t@153))
      $k@168
      $Perm.No)))))
(check-sat)
; unsat
(pop) ; 9
; 0.00s
; (get-info :all-statistics)
(declare-const fvf@171 $FVF<Bool>)
(assert (forall (($r $Ref)) (!
  (implies
    (and
      (and (<= 0 (invOf@164 $r)) (< (invOf@164 $r) $t@160))
      ($Set.in $r ($FVF.domain_Ref__Boolean_value fvf@171)))
    (=
      ($FVF.lookup_Ref__Boolean_value fvf@171 $r)
      ($FVF.lookup_Ref__Boolean_value $t@156 $r)))
  :pattern (($FVF.lookup_Ref__Boolean_value fvf@171 $r) (invOf@164 $r))
  :pattern (($FVF.lookup_Ref__Boolean_value $t@156 $r) (invOf@164 $r)))))
(assert (forall (($r $Ref)) (!
  (implies
    (and
      (ite
        (and (<= 0 (invOf@169 $r)) (< (invOf@169 $r) $t@153))
        (< $Perm.No $k@168)
        false)
      ($Set.in $r ($FVF.domain_Ref__Boolean_value fvf@171)))
    (=
      ($FVF.lookup_Ref__Boolean_value fvf@171 $r)
      ($FVF.lookup_Ref__Boolean_value $t@147 $r)))
  :pattern (($FVF.lookup_Ref__Boolean_value fvf@171 $r) (invOf@169 $r))
  :pattern (($FVF.lookup_Ref__Boolean_value $t@147 $r) (invOf@169 $r)))))
(assert (forall ((k@170 Int)) (!
  (iff
    ($Set.in ($Seq.index $t@159 k@170) ($FVF.domain_Ref__Boolean_value fvf@171))
    (and (and (<= 0 k@170) (< k@170 i@137)) (<= $t@116 $t@123)))
  :pattern (($Set.in
    ($Seq.index $t@159 k@170)
    ($FVF.domain_Ref__Boolean_value fvf@171))))))
; [eval] diz.Set__contents[k].Ref__Boolean_value && x.Set__contents[k].Ref__Boolean_value
; [eval] diz.Set__contents[k]
(set-option :timeout 0)
(push) ; 9
(assert (not (not (= ($Seq.index $t@159 k@170) $Ref.null))))
(check-sat)
; unsat
(pop) ; 9
; 0.00s
; (get-info :all-statistics)
(set-option :timeout 0)
(push) ; 9
(assert (not (<
  $Perm.No
  (+
    (ite
      (and
        (<= 0 (invOf@164 ($Seq.index $t@159 k@170)))
        (< (invOf@164 ($Seq.index $t@159 k@170)) $t@160))
      $Perm.Write
      $Perm.No)
    (ite
      (and
        (<= 0 (invOf@169 ($Seq.index $t@159 k@170)))
        (< (invOf@169 ($Seq.index $t@159 k@170)) $t@153))
      $k@168
      $Perm.No)))))
(check-sat)
; unsat
(pop) ; 9
; 0.00s
; (get-info :all-statistics)
(declare-const fvf@172 $FVF<Bool>)
(push) ; 9
(set-option :timeout 0)
(push) ; 10
(assert (not (not ($FVF.lookup_Ref__Boolean_value fvf@171 ($Seq.index $t@159 k@170)))))
(check-sat)
; unknown
(pop) ; 10
; 0.00s
; (get-info :all-statistics)
(set-option :timeout 0)
(push) ; 10
(assert (not ($FVF.lookup_Ref__Boolean_value fvf@171 ($Seq.index $t@159 k@170))))
(check-sat)
; unknown
(pop) ; 10
; 0.00s
; (get-info :all-statistics)
(push) ; 10
; [then-branch 33] Lookup(Ref__Boolean_value,fvf@171,$t@159[k@170])
(assert ($FVF.lookup_Ref__Boolean_value fvf@171 ($Seq.index $t@159 k@170)))
; [eval] x.Set__contents[k]
(set-option :timeout 0)
(push) ; 11
(assert (not (not (= ($Seq.index $t@150 k@170) $Ref.null))))
(check-sat)
; unsat
(pop) ; 11
; 0.00s
; (get-info :all-statistics)
(set-option :timeout 0)
(push) ; 11
(assert (not (<
  $Perm.No
  (+
    (ite
      (and
        (<= 0 (invOf@164 ($Seq.index $t@150 k@170)))
        (< (invOf@164 ($Seq.index $t@150 k@170)) $t@160))
      $Perm.Write
      $Perm.No)
    (ite
      (and
        (<= 0 (invOf@169 ($Seq.index $t@150 k@170)))
        (< (invOf@169 ($Seq.index $t@150 k@170)) $t@153))
      $k@168
      $Perm.No)))))
(check-sat)
; unsat
(pop) ; 11
; 0.00s
; (get-info :all-statistics)
(declare-const fvf@173 $FVF<Bool>)
(assert (forall (($r $Ref)) (!
  (implies
    (and
      (and (<= 0 (invOf@164 $r)) (< (invOf@164 $r) $t@160))
      ($Set.in $r ($FVF.domain_Ref__Boolean_value fvf@173)))
    (=
      ($FVF.lookup_Ref__Boolean_value fvf@173 $r)
      ($FVF.lookup_Ref__Boolean_value $t@156 $r)))
  :pattern (($FVF.lookup_Ref__Boolean_value fvf@173 $r) (invOf@164 $r))
  :pattern (($FVF.lookup_Ref__Boolean_value $t@156 $r) (invOf@164 $r)))))
(assert (forall (($r $Ref)) (!
  (implies
    (and
      (ite
        (and (<= 0 (invOf@169 $r)) (< (invOf@169 $r) $t@153))
        (< $Perm.No $k@168)
        false)
      ($Set.in $r ($FVF.domain_Ref__Boolean_value fvf@173)))
    (=
      ($FVF.lookup_Ref__Boolean_value fvf@173 $r)
      ($FVF.lookup_Ref__Boolean_value $t@147 $r)))
  :pattern (($FVF.lookup_Ref__Boolean_value fvf@173 $r) (invOf@169 $r))
  :pattern (($FVF.lookup_Ref__Boolean_value $t@147 $r) (invOf@169 $r)))))
(assert (forall ((k@170 Int)) (!
  (iff
    ($Set.in ($Seq.index $t@150 k@170) ($FVF.domain_Ref__Boolean_value fvf@173))
    (and
      ($FVF.lookup_Ref__Boolean_value fvf@171 ($Seq.index $t@159 k@170))
      (and (<= 0 k@170) (< k@170 i@137))
      (<= $t@116 $t@123)))
  :pattern (($Set.in
    ($Seq.index $t@150 k@170)
    ($FVF.domain_Ref__Boolean_value fvf@173))))))
(pop) ; 10
(push) ; 10
; [else-branch 33] !Lookup(Ref__Boolean_value,fvf@171,$t@159[k@170])
(assert (not ($FVF.lookup_Ref__Boolean_value fvf@171 ($Seq.index $t@159 k@170))))
(pop) ; 10
(pop) ; 9
(assert (forall ((k@170 Int)) (!
  (iff
    ($Set.in ($Seq.index $t@150 k@170) ($FVF.domain_Ref__Boolean_value fvf@173))
    (and
      ($FVF.lookup_Ref__Boolean_value fvf@171 ($Seq.index $t@159 k@170))
      (and (<= 0 k@170) (< k@170 i@137))
      (<= $t@116 $t@123)))
  :pattern (($Set.in
    ($Seq.index $t@150 k@170)
    ($FVF.domain_Ref__Boolean_value fvf@173))))))
(assert (forall (($r $Ref)) (!
  (implies
    (and
      (ite
        (and (<= 0 (invOf@169 $r)) (< (invOf@169 $r) $t@153))
        (< $Perm.No $k@168)
        false)
      ($Set.in $r ($FVF.domain_Ref__Boolean_value fvf@173)))
    (=
      ($FVF.lookup_Ref__Boolean_value fvf@173 $r)
      ($FVF.lookup_Ref__Boolean_value $t@147 $r)))
  :pattern (($FVF.lookup_Ref__Boolean_value fvf@173 $r) (invOf@169 $r))
  :pattern (($FVF.lookup_Ref__Boolean_value $t@147 $r) (invOf@169 $r)))))
(assert (forall (($r $Ref)) (!
  (implies
    (and
      (and (<= 0 (invOf@164 $r)) (< (invOf@164 $r) $t@160))
      ($Set.in $r ($FVF.domain_Ref__Boolean_value fvf@173)))
    (=
      ($FVF.lookup_Ref__Boolean_value fvf@173 $r)
      ($FVF.lookup_Ref__Boolean_value $t@156 $r)))
  :pattern (($FVF.lookup_Ref__Boolean_value fvf@173 $r) (invOf@164 $r))
  :pattern (($FVF.lookup_Ref__Boolean_value $t@156 $r) (invOf@164 $r)))))
(pop) ; 8
(push) ; 8
; [else-branch 32] !0 <= k@170 && k@170 < i@137
(assert (not (and (<= 0 k@170) (< k@170 i@137))))
(pop) ; 8
(pop) ; 7
(assert (forall (($r $Ref)) (!
  (implies
    (and
      (and (<= 0 (invOf@164 $r)) (< (invOf@164 $r) $t@160))
      ($Set.in $r ($FVF.domain_Ref__Boolean_value fvf@173)))
    (=
      ($FVF.lookup_Ref__Boolean_value fvf@173 $r)
      ($FVF.lookup_Ref__Boolean_value $t@156 $r)))
  :pattern (($FVF.lookup_Ref__Boolean_value fvf@173 $r) (invOf@164 $r))
  :pattern (($FVF.lookup_Ref__Boolean_value $t@156 $r) (invOf@164 $r)))))
(assert (forall (($r $Ref)) (!
  (implies
    (and
      (ite
        (and (<= 0 (invOf@169 $r)) (< (invOf@169 $r) $t@153))
        (< $Perm.No $k@168)
        false)
      ($Set.in $r ($FVF.domain_Ref__Boolean_value fvf@173)))
    (=
      ($FVF.lookup_Ref__Boolean_value fvf@173 $r)
      ($FVF.lookup_Ref__Boolean_value $t@147 $r)))
  :pattern (($FVF.lookup_Ref__Boolean_value fvf@173 $r) (invOf@169 $r))
  :pattern (($FVF.lookup_Ref__Boolean_value $t@147 $r) (invOf@169 $r)))))
(assert (forall ((k@170 Int)) (!
  (iff
    ($Set.in ($Seq.index $t@150 k@170) ($FVF.domain_Ref__Boolean_value fvf@173))
    (and
      ($FVF.lookup_Ref__Boolean_value fvf@171 ($Seq.index $t@159 k@170))
      (and (<= 0 k@170) (< k@170 i@137))
      (<= $t@116 $t@123)))
  :pattern (($Set.in
    ($Seq.index $t@150 k@170)
    ($FVF.domain_Ref__Boolean_value fvf@173))))))
(assert (forall ((k@170 Int)) (!
  (iff
    ($Set.in ($Seq.index $t@159 k@170) ($FVF.domain_Ref__Boolean_value fvf@171))
    (and (and (<= 0 k@170) (< k@170 i@137)) (<= $t@116 $t@123)))
  :pattern (($Set.in
    ($Seq.index $t@159 k@170)
    ($FVF.domain_Ref__Boolean_value fvf@171))))))
(assert (forall (($r $Ref)) (!
  (implies
    (and
      (ite
        (and (<= 0 (invOf@169 $r)) (< (invOf@169 $r) $t@153))
        (< $Perm.No $k@168)
        false)
      ($Set.in $r ($FVF.domain_Ref__Boolean_value fvf@171)))
    (=
      ($FVF.lookup_Ref__Boolean_value fvf@171 $r)
      ($FVF.lookup_Ref__Boolean_value $t@147 $r)))
  :pattern (($FVF.lookup_Ref__Boolean_value fvf@171 $r) (invOf@169 $r))
  :pattern (($FVF.lookup_Ref__Boolean_value $t@147 $r) (invOf@169 $r)))))
(assert (forall (($r $Ref)) (!
  (implies
    (and
      (and (<= 0 (invOf@164 $r)) (< (invOf@164 $r) $t@160))
      ($Set.in $r ($FVF.domain_Ref__Boolean_value fvf@171)))
    (=
      ($FVF.lookup_Ref__Boolean_value fvf@171 $r)
      ($FVF.lookup_Ref__Boolean_value $t@156 $r)))
  :pattern (($FVF.lookup_Ref__Boolean_value fvf@171 $r) (invOf@164 $r))
  :pattern (($FVF.lookup_Ref__Boolean_value $t@156 $r) (invOf@164 $r)))))
(pop) ; 6
(assert (forall (($r $Ref)) (!
  (implies
    (and
      (and (<= 0 (invOf@164 $r)) (< (invOf@164 $r) $t@160))
      ($Set.in $r ($FVF.domain_Ref__Boolean_value fvf@173)))
    (=
      ($FVF.lookup_Ref__Boolean_value fvf@173 $r)
      ($FVF.lookup_Ref__Boolean_value $t@156 $r)))
  :pattern (($FVF.lookup_Ref__Boolean_value fvf@173 $r) (invOf@164 $r))
  :pattern (($FVF.lookup_Ref__Boolean_value $t@156 $r) (invOf@164 $r)))))
(assert (forall (($r $Ref)) (!
  (implies
    (and
      (ite
        (and (<= 0 (invOf@169 $r)) (< (invOf@169 $r) $t@153))
        (< $Perm.No $k@168)
        false)
      ($Set.in $r ($FVF.domain_Ref__Boolean_value fvf@173)))
    (=
      ($FVF.lookup_Ref__Boolean_value fvf@173 $r)
      ($FVF.lookup_Ref__Boolean_value $t@147 $r)))
  :pattern (($FVF.lookup_Ref__Boolean_value fvf@173 $r) (invOf@169 $r))
  :pattern (($FVF.lookup_Ref__Boolean_value $t@147 $r) (invOf@169 $r)))))
(assert (forall ((k@170 Int)) (!
  (iff
    ($Set.in ($Seq.index $t@150 k@170) ($FVF.domain_Ref__Boolean_value fvf@173))
    (and
      ($FVF.lookup_Ref__Boolean_value fvf@171 ($Seq.index $t@159 k@170))
      (and (<= 0 k@170) (< k@170 i@137))
      (<= $t@116 $t@123)))
  :pattern (($Set.in
    ($Seq.index $t@150 k@170)
    ($FVF.domain_Ref__Boolean_value fvf@173))))))
(assert (forall ((k@170 Int)) (!
  (iff
    ($Set.in ($Seq.index $t@159 k@170) ($FVF.domain_Ref__Boolean_value fvf@171))
    (and (and (<= 0 k@170) (< k@170 i@137)) (<= $t@116 $t@123)))
  :pattern (($Set.in
    ($Seq.index $t@159 k@170)
    ($FVF.domain_Ref__Boolean_value fvf@171))))))
(assert (forall (($r $Ref)) (!
  (implies
    (and
      (ite
        (and (<= 0 (invOf@169 $r)) (< (invOf@169 $r) $t@153))
        (< $Perm.No $k@168)
        false)
      ($Set.in $r ($FVF.domain_Ref__Boolean_value fvf@171)))
    (=
      ($FVF.lookup_Ref__Boolean_value fvf@171 $r)
      ($FVF.lookup_Ref__Boolean_value $t@147 $r)))
  :pattern (($FVF.lookup_Ref__Boolean_value fvf@171 $r) (invOf@169 $r))
  :pattern (($FVF.lookup_Ref__Boolean_value $t@147 $r) (invOf@169 $r)))))
(assert (forall (($r $Ref)) (!
  (implies
    (and
      (and (<= 0 (invOf@164 $r)) (< (invOf@164 $r) $t@160))
      ($Set.in $r ($FVF.domain_Ref__Boolean_value fvf@171)))
    (=
      ($FVF.lookup_Ref__Boolean_value fvf@171 $r)
      ($FVF.lookup_Ref__Boolean_value $t@156 $r)))
  :pattern (($FVF.lookup_Ref__Boolean_value fvf@171 $r) (invOf@164 $r))
  :pattern (($FVF.lookup_Ref__Boolean_value $t@156 $r) (invOf@164 $r)))))
(assert (forall ((k@170 Int)) (!
  (implies
    (and (<= 0 k@170) (< k@170 i@137))
    (=
      ($FVF.lookup_Ref__Boolean_value fvf@171 ($Seq.index $t@159 k@170))
      (and
        ($FVF.lookup_Ref__Boolean_value fvf@171 ($Seq.index $t@159 k@170))
        ($FVF.lookup_Ref__Boolean_value fvf@173 ($Seq.index $t@150 k@170)))))
  :pattern (($Seq.index $t@159 k@170))
  :pattern (($Seq.index $t@159 k@170))
  :pattern (($Seq.index $t@150 k@170)))))
; [eval] i < diz.Set__max
(assert (< i@137 $t@160))
(set-option :timeout 0)
(check-sat)
; unknown
; [exec]
; __flatten_8 := diz.Set__contents[i]
; [eval] diz.Set__contents[i]
; [exec]
; __flatten_10 := diz.Set__contents[i]
; [eval] diz.Set__contents[i]
; [exec]
; __flatten_11 := x.Set__contents[i]
; [eval] x.Set__contents[i]
; [exec]
; __flatten_9 := __flatten_10.Ref__Boolean_value && __flatten_11.Ref__Boolean_value
; [eval] __flatten_10.Ref__Boolean_value && __flatten_11.Ref__Boolean_value
(set-option :timeout 0)
(push) ; 6
(assert (not (not (= ($Seq.index $t@159 i@137) $Ref.null))))
(check-sat)
; unsat
(pop) ; 6
; 0.00s
; (get-info :all-statistics)
(set-option :timeout 0)
(push) ; 6
(assert (not (<
  $Perm.No
  (+
    (ite
      (and
        (<= 0 (invOf@164 ($Seq.index $t@159 i@137)))
        (< (invOf@164 ($Seq.index $t@159 i@137)) $t@160))
      $Perm.Write
      $Perm.No)
    (ite
      (and
        (<= 0 (invOf@169 ($Seq.index $t@159 i@137)))
        (< (invOf@169 ($Seq.index $t@159 i@137)) $t@153))
      $k@168
      $Perm.No)))))
(check-sat)
; unsat
(pop) ; 6
; 0.00s
; (get-info :all-statistics)
(declare-const fvf@174 $FVF<Bool>)
(assert (implies
  (and
    (<= 0 (invOf@164 ($Seq.index $t@159 i@137)))
    (< (invOf@164 ($Seq.index $t@159 i@137)) $t@160))
  (=
    ($FVF.lookup_Ref__Boolean_value fvf@174 ($Seq.index $t@159 i@137))
    ($FVF.lookup_Ref__Boolean_value $t@156 ($Seq.index $t@159 i@137)))))
(assert (implies
  (ite
    (and
      (<= 0 (invOf@169 ($Seq.index $t@159 i@137)))
      (< (invOf@169 ($Seq.index $t@159 i@137)) $t@153))
    (< $Perm.No $k@168)
    false)
  (=
    ($FVF.lookup_Ref__Boolean_value fvf@174 ($Seq.index $t@159 i@137))
    ($FVF.lookup_Ref__Boolean_value $t@147 ($Seq.index $t@159 i@137)))))
(assert ($Set.equal
  ($FVF.domain_Ref__Boolean_value fvf@174)
  ($Set.singleton  ($Seq.index $t@159 i@137))))
(push) ; 6
(set-option :timeout 0)
(push) ; 7
(assert (not (not ($FVF.lookup_Ref__Boolean_value fvf@174 ($Seq.index $t@159 i@137)))))
(check-sat)
; unknown
(pop) ; 7
; 0.00s
; (get-info :all-statistics)
(set-option :timeout 0)
(push) ; 7
(assert (not ($FVF.lookup_Ref__Boolean_value fvf@174 ($Seq.index $t@159 i@137))))
(check-sat)
; unknown
(pop) ; 7
; 0.00s
; (get-info :all-statistics)
(push) ; 7
; [then-branch 34] Lookup(Ref__Boolean_value,fvf@174,$t@159[i@137])
(assert ($FVF.lookup_Ref__Boolean_value fvf@174 ($Seq.index $t@159 i@137)))
(set-option :timeout 0)
(push) ; 8
(assert (not (not (= ($Seq.index $t@150 i@137) $Ref.null))))
(check-sat)
; unsat
(pop) ; 8
; 0.00s
; (get-info :all-statistics)
(set-option :timeout 0)
(push) ; 8
(assert (not (<
  $Perm.No
  (+
    (ite
      (and
        (<= 0 (invOf@164 ($Seq.index $t@150 i@137)))
        (< (invOf@164 ($Seq.index $t@150 i@137)) $t@160))
      $Perm.Write
      $Perm.No)
    (ite
      (and
        (<= 0 (invOf@169 ($Seq.index $t@150 i@137)))
        (< (invOf@169 ($Seq.index $t@150 i@137)) $t@153))
      $k@168
      $Perm.No)))))
(check-sat)
; unsat
(pop) ; 8
; 0.00s
; (get-info :all-statistics)
(declare-const fvf@175 $FVF<Bool>)
(assert (implies
  (and
    (<= 0 (invOf@164 ($Seq.index $t@150 i@137)))
    (< (invOf@164 ($Seq.index $t@150 i@137)) $t@160))
  (=
    ($FVF.lookup_Ref__Boolean_value fvf@175 ($Seq.index $t@150 i@137))
    ($FVF.lookup_Ref__Boolean_value $t@156 ($Seq.index $t@150 i@137)))))
(assert (implies
  (ite
    (and
      (<= 0 (invOf@169 ($Seq.index $t@150 i@137)))
      (< (invOf@169 ($Seq.index $t@150 i@137)) $t@153))
    (< $Perm.No $k@168)
    false)
  (=
    ($FVF.lookup_Ref__Boolean_value fvf@175 ($Seq.index $t@150 i@137))
    ($FVF.lookup_Ref__Boolean_value $t@147 ($Seq.index $t@150 i@137)))))
(assert ($Set.equal
  ($FVF.domain_Ref__Boolean_value fvf@175)
  ($Set.singleton  ($Seq.index $t@150 i@137))))
(pop) ; 7
(push) ; 7
; [else-branch 34] !Lookup(Ref__Boolean_value,fvf@174,$t@159[i@137])
(assert (not ($FVF.lookup_Ref__Boolean_value fvf@174 ($Seq.index $t@159 i@137))))
(pop) ; 7
(pop) ; 6
(assert ($Set.equal
  ($FVF.domain_Ref__Boolean_value fvf@175)
  ($Set.singleton  ($Seq.index $t@150 i@137))))
(assert (implies
  (ite
    (and
      (<= 0 (invOf@169 ($Seq.index $t@150 i@137)))
      (< (invOf@169 ($Seq.index $t@150 i@137)) $t@153))
    (< $Perm.No $k@168)
    false)
  (=
    ($FVF.lookup_Ref__Boolean_value fvf@175 ($Seq.index $t@150 i@137))
    ($FVF.lookup_Ref__Boolean_value $t@147 ($Seq.index $t@150 i@137)))))
(assert (implies
  (and
    (<= 0 (invOf@164 ($Seq.index $t@150 i@137)))
    (< (invOf@164 ($Seq.index $t@150 i@137)) $t@160))
  (=
    ($FVF.lookup_Ref__Boolean_value fvf@175 ($Seq.index $t@150 i@137))
    ($FVF.lookup_Ref__Boolean_value $t@156 ($Seq.index $t@150 i@137)))))
; [exec]
; __flatten_8.Ref__Boolean_value := __flatten_9
(set-option :timeout 0)
(push) ; 6
(assert (not (not (= ($Seq.index $t@159 i@137) $Ref.null))))
(check-sat)
; unsat
(pop) ; 6
; 0.00s
; (get-info :all-statistics)
(declare-const fvf@176 $FVF<Bool>)
; Precomputing split data for $t@159[i@137].Ref__Boolean_value # W
(define-fun $permsTaken7 (($r $Ref)) $Perm
  ($Perm.min
    (ite (= $r ($Seq.index $t@159 i@137)) $Perm.Write $Perm.No)
    (ite
      (= $r ($Seq.index $t@159 i@137))
      (ite
        (and (<= 0 (invOf@164 $r)) (< (invOf@164 $r) $t@160))
        $Perm.Write
        $Perm.No)
      $Perm.No)))
(define-fun $permsTaken8 (($r $Ref)) $Perm
  ($Perm.min
    (-
      (ite (= $r ($Seq.index $t@159 i@137)) $Perm.Write $Perm.No)
      ($permsTaken7 $r))
    (ite
      (= $r ($Seq.index $t@159 i@137))
      (ite (and (<= 0 (invOf@169 $r)) (< (invOf@169 $r) $t@153)) $k@168 $Perm.No)
      $Perm.No)))
; Done precomputing, updating quantified heap chunks
; Chunk depleted?
(set-option :timeout 500)
(push) ; 6
(assert (not (forall (($r $Ref)) (!
  (=
    (-
      (ite
        (and (<= 0 (invOf@164 $r)) (< (invOf@164 $r) $t@160))
        $Perm.Write
        $Perm.No)
      ($permsTaken7 $r))
    $Perm.No)
  ))))
(check-sat)
; unknown
(pop) ; 6
; 0.01s
; (get-info :all-statistics)
; Enough permissions taken?
(set-option :timeout 500)
(push) ; 6
(assert (not (= (- $Perm.Write ($permsTaken7 ($Seq.index $t@159 i@137))) $Perm.No)))
(check-sat)
; unsat
(pop) ; 6
; 0.00s
; (get-info :all-statistics)
; Final check that enough permissions have been taken
; Done splitting
(declare-const fvf@177 $FVF<Bool>)
(assert (=
  ($FVF.lookup_Ref__Boolean_value fvf@177 ($Seq.index $t@159 i@137))
  (and
    ($FVF.lookup_Ref__Boolean_value fvf@174 ($Seq.index $t@159 i@137))
    ($FVF.lookup_Ref__Boolean_value fvf@175 ($Seq.index $t@150 i@137)))))
(assert ($Set.equal
  ($FVF.domain_Ref__Boolean_value fvf@177)
  ($Set.singleton  ($Seq.index $t@159 i@137))))
; [exec]
; i := i + 1
; [eval] i + 1
(declare-const $k@178 $Perm)
(assert ($Perm.isValidVar $k@178))
(assert ($Perm.isReadVar $k@178 $Perm.Write))
(set-option :timeout 0)
(push) ; 6
(assert (not (or (= $k@178 $Perm.No) true)))
(check-sat)
; unsat
(pop) ; 6
; 0.00s
; (get-info :all-statistics)
(assert (< $k@178 $k@161))
; [eval] diz.Set__max > 0
(declare-const $k@179 $Perm)
(assert ($Perm.isValidVar $k@179))
(assert ($Perm.isReadVar $k@179 $Perm.Write))
(set-option :timeout 0)
(push) ; 6
(assert (not (or (= $k@179 $Perm.No) true)))
(check-sat)
; unsat
(pop) ; 6
; 0.00s
; (get-info :all-statistics)
(assert (< $k@179 $k@162))
; [eval] |diz.Set__contents| == diz.Set__max
; [eval] |diz.Set__contents|
(declare-const fvf@180 $FVF<Int>)
(declare-const fvf@181 $FVF<Int>)
(declare-const fvf@182 $FVF<$Seq<$Ref>>)
(declare-const fvf@183 $FVF<$Seq<$Ref>>)
(assert (= ($FVF.lookup_Set__max fvf@180 x@102) $t@153))
(assert ($Set.equal ($FVF.domain_Set__max fvf@180) ($Set.singleton  x@102)))
(assert (= ($FVF.lookup_Set__max fvf@181 diz@101) $t@160))
(assert ($Set.equal ($FVF.domain_Set__max fvf@181) ($Set.singleton  diz@101)))
(assert ($Seq.equal ($FVF.lookup_Set__contents fvf@182 x@102) $t@150))
(assert ($Set.equal ($FVF.domain_Set__contents fvf@182) ($Set.singleton  x@102)))
(assert ($Seq.equal ($FVF.lookup_Set__contents fvf@183 diz@101) $t@159))
(assert ($Set.equal ($FVF.domain_Set__contents fvf@183) ($Set.singleton  diz@101)))
(declare-const k@184 Int)
; [eval] (0 <= k) && (k < diz.Set__max)
; [eval] 0 <= k
(push) ; 6
(set-option :timeout 0)
(push) ; 7
(assert (not (not (<= 0 k@184))))
(check-sat)
; unknown
(pop) ; 7
; 0.01s
; (get-info :all-statistics)
(set-option :timeout 0)
(push) ; 7
(assert (not (<= 0 k@184)))
(check-sat)
; unknown
(pop) ; 7
; 0.01s
; (get-info :all-statistics)
(push) ; 7
; [then-branch 35] 0 <= k@184
(assert (<= 0 k@184))
; [eval] k < diz.Set__max
(set-option :timeout 0)
(push) ; 8
(assert (not (< $Perm.No (+ (ite (= diz@101 x@102) $k@165 $Perm.No) $k@161))))
(check-sat)
; unsat
(pop) ; 8
; 0.00s
; (get-info :all-statistics)
(declare-const fvf@185 $FVF<Int>)
(assert (implies
  (ite (= diz@101 x@102) (< $Perm.No $k@165) false)
  (=
    ($FVF.lookup_Set__max fvf@185 diz@101)
    ($FVF.lookup_Set__max fvf@180 diz@101))))
(assert (implies
  (< $Perm.No $k@161)
  (=
    ($FVF.lookup_Set__max fvf@185 diz@101)
    ($FVF.lookup_Set__max fvf@181 diz@101))))
(assert ($Set.equal ($FVF.domain_Set__max fvf@185) ($Set.singleton  diz@101)))
(pop) ; 7
(push) ; 7
; [else-branch 35] !0 <= k@184
(assert (not (<= 0 k@184)))
(pop) ; 7
(pop) ; 6
(assert ($Set.equal ($FVF.domain_Set__max fvf@185) ($Set.singleton  diz@101)))
(assert (implies
  (< $Perm.No $k@161)
  (=
    ($FVF.lookup_Set__max fvf@185 diz@101)
    ($FVF.lookup_Set__max fvf@181 diz@101))))
(assert (implies
  (ite (= diz@101 x@102) (< $Perm.No $k@165) false)
  (=
    ($FVF.lookup_Set__max fvf@185 diz@101)
    ($FVF.lookup_Set__max fvf@180 diz@101))))
(set-option :timeout 0)
(push) ; 6
(assert (not (not (and (<= 0 k@184) (< k@184 ($FVF.lookup_Set__max fvf@185 diz@101))))))
(check-sat)
; unknown
(pop) ; 6
; 0.01s
; (get-info :all-statistics)
(assert (and (<= 0 k@184) (< k@184 ($FVF.lookup_Set__max fvf@185 diz@101))))
; [eval] diz.Set__contents[k]
(set-option :timeout 0)
(push) ; 6
(assert (not (< $Perm.No (+ (ite (= diz@101 x@102) $k@166 $Perm.No) $k@162))))
(check-sat)
; unsat
(pop) ; 6
; 0.00s
; (get-info :all-statistics)
(declare-const fvf@186 $FVF<$Seq<$Ref>>)
(assert (implies
  (ite (= diz@101 x@102) (< $Perm.No $k@166) false)
  ($Seq.equal
    ($FVF.lookup_Set__contents fvf@186 diz@101)
    ($FVF.lookup_Set__contents fvf@182 diz@101))))
(assert (implies
  (< $Perm.No $k@162)
  ($Seq.equal
    ($FVF.lookup_Set__contents fvf@186 diz@101)
    ($FVF.lookup_Set__contents fvf@183 diz@101))))
(assert ($Set.equal ($FVF.domain_Set__contents fvf@186) ($Set.singleton  diz@101)))
(set-option :timeout 0)
(push) ; 6
(assert (not (forall (($x Int) ($y Int)) (!
  (implies
    (and
      (and (<= 0 $x) (< $x ($FVF.lookup_Set__max fvf@185 diz@101)))
      (and (<= 0 $y) (< $y ($FVF.lookup_Set__max fvf@185 diz@101)))
      (=
        ($Seq.index ($FVF.lookup_Set__contents fvf@186 diz@101) $x)
        ($Seq.index ($FVF.lookup_Set__contents fvf@186 diz@101) $y)))
    (= $x $y))
  :pattern (($Seq.index ($FVF.lookup_Set__contents fvf@186 diz@101) $x) ($Seq.index
    ($FVF.lookup_Set__contents fvf@186 diz@101)
    $y))))))
(check-sat)
; unsat
(pop) ; 6
; 0.00s
; (get-info :all-statistics)
(declare-fun invOf@187 ($Ref) Int)
(assert (forall (($r $Ref)) (!
  (implies
    (and
      (<= 0 (invOf@187 $r))
      (< (invOf@187 $r) ($FVF.lookup_Set__max fvf@185 diz@101)))
    (=
      ($Seq.index ($FVF.lookup_Set__contents fvf@186 diz@101) (invOf@187 $r))
      $r))
  :pattern ((invOf@187 $r)))))
(assert (forall ((k@184 Int)) (!
  (implies
    (and (<= 0 k@184) (< k@184 ($FVF.lookup_Set__max fvf@185 diz@101)))
    (=
      (invOf@187 ($Seq.index ($FVF.lookup_Set__contents fvf@186 diz@101) k@184))
      k@184))
  :pattern (($Seq.index ($FVF.lookup_Set__contents fvf@186 diz@101) k@184)))))
(declare-const fvf@188 $FVF<Bool>)
; Precomputing split data for Lookup(Set__contents,fvf@186,diz@101)[k@184].Ref__Boolean_value # W
(define-fun $permsTaken9 (($r $Ref)) $Perm
  ($Perm.min
    (ite
      (and
        (<= 0 (invOf@187 $r))
        (< (invOf@187 $r) ($FVF.lookup_Set__max fvf@185 diz@101)))
      $Perm.Write
      $Perm.No)
    (ite
      (= $r ($Seq.index ($FVF.lookup_Set__contents fvf@186 diz@101) k@184))
      (ite (= $r ($Seq.index $t@159 i@137)) $Perm.Write $Perm.No)
      $Perm.No)))
(define-fun $permsTaken10 (($r $Ref)) $Perm
  ($Perm.min
    (-
      (ite
        (and
          (<= 0 (invOf@187 $r))
          (< (invOf@187 $r) ($FVF.lookup_Set__max fvf@185 diz@101)))
        $Perm.Write
        $Perm.No)
      ($permsTaken9 $r))
    (ite
      (= $r ($Seq.index ($FVF.lookup_Set__contents fvf@186 diz@101) k@184))
      (-
        (ite
          (and (<= 0 (invOf@164 $r)) (< (invOf@164 $r) $t@160))
          $Perm.Write
          $Perm.No)
        ($permsTaken7 $r))
      $Perm.No)))
(define-fun $permsTaken11 (($r $Ref)) $Perm
  ($Perm.min
    (-
      (-
        (ite
          (and
            (<= 0 (invOf@187 $r))
            (< (invOf@187 $r) ($FVF.lookup_Set__max fvf@185 diz@101)))
          $Perm.Write
          $Perm.No)
        ($permsTaken9 $r))
      ($permsTaken10 $r))
    (ite
      (= $r ($Seq.index ($FVF.lookup_Set__contents fvf@186 diz@101) k@184))
      (ite (and (<= 0 (invOf@169 $r)) (< (invOf@169 $r) $t@153)) $k@168 $Perm.No)
      $Perm.No)))
; Done precomputing, updating quantified heap chunks
; Chunk depleted?
(set-option :timeout 500)
(push) ; 6
(assert (not (forall (($r $Ref)) (!
  (=
    (-
      (ite (= $r ($Seq.index $t@159 i@137)) $Perm.Write $Perm.No)
      ($permsTaken9 $r))
    $Perm.No)
  ))))
(check-sat)
; unknown
(pop) ; 6
; 0.01s
; (get-info :all-statistics)
; Enough permissions taken?
(set-option :timeout 500)
(push) ; 6
(assert (not (=
  (-
    (ite
      (and
        (<=
          0
          (invOf@187 ($Seq.index
            ($FVF.lookup_Set__contents fvf@186 diz@101)
            k@184)))
        (<
          (invOf@187 ($Seq.index
            ($FVF.lookup_Set__contents fvf@186 diz@101)
            k@184))
          ($FVF.lookup_Set__max fvf@185 diz@101)))
      $Perm.Write
      $Perm.No)
    ($permsTaken9 ($Seq.index ($FVF.lookup_Set__contents fvf@186 diz@101) k@184)))
  $Perm.No)))
(check-sat)
; unknown
(pop) ; 6
; 0.01s
; (get-info :all-statistics)
; Chunk depleted?
(set-option :timeout 500)
(push) ; 6
(assert (not (forall (($r $Ref)) (!
  (=
    (-
      (-
        (ite
          (and (<= 0 (invOf@164 $r)) (< (invOf@164 $r) $t@160))
          $Perm.Write
          $Perm.No)
        ($permsTaken7 $r))
      ($permsTaken10 $r))
    $Perm.No)
  ))))
(check-sat)
; unknown
(pop) ; 6
; 0.02s
; (get-info :all-statistics)
; Enough permissions taken?
(set-option :timeout 500)
(push) ; 6
(assert (not (=
  (-
    (-
      (ite
        (and
          (<=
            0
            (invOf@187 ($Seq.index
              ($FVF.lookup_Set__contents fvf@186 diz@101)
              k@184)))
          (<
            (invOf@187 ($Seq.index
              ($FVF.lookup_Set__contents fvf@186 diz@101)
              k@184))
            ($FVF.lookup_Set__max fvf@185 diz@101)))
        $Perm.Write
        $Perm.No)
      ($permsTaken9 ($Seq.index
        ($FVF.lookup_Set__contents fvf@186 diz@101)
        k@184)))
    ($permsTaken10 ($Seq.index ($FVF.lookup_Set__contents fvf@186 diz@101) k@184)))
  $Perm.No)))
(check-sat)
; unsat
(pop) ; 6
; 0.00s
; (get-info :all-statistics)
; Final check that enough permissions have been taken
; Done splitting
(assert (forall (($r $Ref)) (!
  (implies
    (and
      (ite
        (and (<= 0 (invOf@169 $r)) (< (invOf@169 $r) $t@153))
        (< $Perm.No $k@168)
        false)
      ($Set.in $r ($FVF.domain_Ref__Boolean_value fvf@188)))
    (=
      ($FVF.lookup_Ref__Boolean_value fvf@188 $r)
      ($FVF.lookup_Ref__Boolean_value $t@147 $r)))
  :pattern (($FVF.lookup_Ref__Boolean_value fvf@188 $r) (invOf@169 $r))
  :pattern (($FVF.lookup_Ref__Boolean_value $t@147 $r) (invOf@169 $r)))))
(assert (forall (($r $Ref)) (!
  (implies
    (and
      (<
        $Perm.No
        (-
          (ite
            (and (<= 0 (invOf@164 $r)) (< (invOf@164 $r) $t@160))
            $Perm.Write
            $Perm.No)
          ($permsTaken7 $r)))
      ($Set.in $r ($FVF.domain_Ref__Boolean_value fvf@188)))
    (=
      ($FVF.lookup_Ref__Boolean_value fvf@188 $r)
      ($FVF.lookup_Ref__Boolean_value $t@156 $r)))
  :pattern (($FVF.lookup_Ref__Boolean_value fvf@188 $r) (invOf@164 $r))
  :pattern (($FVF.lookup_Ref__Boolean_value $t@156 $r) (invOf@164 $r)))))
(assert (forall (($r $Ref)) (!
  (implies
    (and
      (= $r ($Seq.index $t@159 i@137))
      ($Set.in $r ($FVF.domain_Ref__Boolean_value fvf@188)))
    (=
      ($FVF.lookup_Ref__Boolean_value fvf@188 $r)
      ($FVF.lookup_Ref__Boolean_value fvf@177 $r)))
  :pattern (($FVF.lookup_Ref__Boolean_value fvf@188 $r))
  :pattern (($FVF.lookup_Ref__Boolean_value fvf@177 $r)))))
(assert (forall (($r $Ref)) (!
  (iff
    ($Set.in $r ($FVF.domain_Ref__Boolean_value fvf@188))
    (and
      (<= 0 (invOf@187 $r))
      (< (invOf@187 $r) ($FVF.lookup_Set__max fvf@185 diz@101))))
  :pattern (($Set.in $r ($FVF.domain_Ref__Boolean_value fvf@188))))))
; [eval] x != null
(declare-const $k@189 $Perm)
(assert ($Perm.isValidVar $k@189))
(assert ($Perm.isReadVar $k@189 $Perm.Write))
(set-option :timeout 0)
(push) ; 6
(assert (not (or (= $k@189 $Perm.No) true)))
(check-sat)
; unsat
(pop) ; 6
; 0.00s
; (get-info :all-statistics)
(assert (< $k@189 $k@165))
; [eval] x.Set__max > 0
(declare-const $k@190 $Perm)
(assert ($Perm.isValidVar $k@190))
(assert ($Perm.isReadVar $k@190 $Perm.Write))
(set-option :timeout 0)
(push) ; 6
(assert (not (or (= $k@190 $Perm.No) true)))
(check-sat)
; unsat
(pop) ; 6
; 0.00s
; (get-info :all-statistics)
(assert (< $k@190 $k@166))
; [eval] x.Set__max >= diz.Set__max
(declare-const fvf@191 $FVF<Int>)
(declare-const fvf@192 $FVF<Int>)
(declare-const fvf@193 $FVF<$Seq<$Ref>>)
(declare-const fvf@194 $FVF<$Seq<$Ref>>)
(assert (= ($FVF.lookup_Set__max fvf@191 x@102) $t@153))
(assert ($Set.equal ($FVF.domain_Set__max fvf@191) ($Set.singleton  x@102)))
(assert (= ($FVF.lookup_Set__max fvf@192 diz@101) $t@160))
(assert ($Set.equal ($FVF.domain_Set__max fvf@192) ($Set.singleton  diz@101)))
(assert ($Seq.equal ($FVF.lookup_Set__contents fvf@193 x@102) $t@150))
(assert ($Set.equal ($FVF.domain_Set__contents fvf@193) ($Set.singleton  x@102)))
(assert ($Seq.equal ($FVF.lookup_Set__contents fvf@194 diz@101) $t@159))
(assert ($Set.equal ($FVF.domain_Set__contents fvf@194) ($Set.singleton  diz@101)))
(declare-const k@195 Int)
; [eval] (0 <= k) && (k < x.Set__max)
; [eval] 0 <= k
(push) ; 6
(set-option :timeout 0)
(push) ; 7
(assert (not (not (<= 0 k@195))))
(check-sat)
; unknown
(pop) ; 7
; 0.01s
; (get-info :all-statistics)
(set-option :timeout 0)
(push) ; 7
(assert (not (<= 0 k@195)))
(check-sat)
; unknown
(pop) ; 7
; 0.01s
; (get-info :all-statistics)
(push) ; 7
; [then-branch 36] 0 <= k@195
(assert (<= 0 k@195))
; [eval] k < x.Set__max
(set-option :timeout 0)
(push) ; 8
(assert (not (< $Perm.No (+ $k@165 (ite (= x@102 diz@101) $k@161 $Perm.No)))))
(check-sat)
; unsat
(pop) ; 8
; 0.00s
; (get-info :all-statistics)
(declare-const fvf@196 $FVF<Int>)
(assert (implies
  (< $Perm.No $k@165)
  (= ($FVF.lookup_Set__max fvf@196 x@102) ($FVF.lookup_Set__max fvf@191 x@102))))
(assert (implies
  (ite (= x@102 diz@101) (< $Perm.No $k@161) false)
  (= ($FVF.lookup_Set__max fvf@196 x@102) ($FVF.lookup_Set__max fvf@192 x@102))))
(assert ($Set.equal ($FVF.domain_Set__max fvf@196) ($Set.singleton  x@102)))
(pop) ; 7
(push) ; 7
; [else-branch 36] !0 <= k@195
(assert (not (<= 0 k@195)))
(pop) ; 7
(pop) ; 6
(assert ($Set.equal ($FVF.domain_Set__max fvf@196) ($Set.singleton  x@102)))
(assert (implies
  (ite (= x@102 diz@101) (< $Perm.No $k@161) false)
  (= ($FVF.lookup_Set__max fvf@196 x@102) ($FVF.lookup_Set__max fvf@192 x@102))))
(assert (implies
  (< $Perm.No $k@165)
  (= ($FVF.lookup_Set__max fvf@196 x@102) ($FVF.lookup_Set__max fvf@191 x@102))))
(set-option :timeout 0)
(push) ; 6
(assert (not (not (and (<= 0 k@195) (< k@195 ($FVF.lookup_Set__max fvf@196 x@102))))))
(check-sat)
; unknown
(pop) ; 6
; 0.01s
; (get-info :all-statistics)
(assert (and (<= 0 k@195) (< k@195 ($FVF.lookup_Set__max fvf@196 x@102))))
(declare-const $k@197 $Perm)
(assert ($Perm.isValidVar $k@197))
(assert ($Perm.isReadVar $k@197 $Perm.Write))
(set-option :timeout 0)
(push) ; 6
(assert (not (or (= $k@197 $Perm.No) true)))
(check-sat)
; unsat
(pop) ; 6
; 0.00s
; (get-info :all-statistics)
; [eval] x.Set__contents[k]
(set-option :timeout 0)
(push) ; 6
(assert (not (< $Perm.No (+ $k@166 (ite (= x@102 diz@101) $k@162 $Perm.No)))))
(check-sat)
; unsat
(pop) ; 6
; 0.00s
; (get-info :all-statistics)
(declare-const fvf@198 $FVF<$Seq<$Ref>>)
(assert (implies
  (< $Perm.No $k@166)
  ($Seq.equal
    ($FVF.lookup_Set__contents fvf@198 x@102)
    ($FVF.lookup_Set__contents fvf@193 x@102))))
(assert (implies
  (ite (= x@102 diz@101) (< $Perm.No $k@162) false)
  ($Seq.equal
    ($FVF.lookup_Set__contents fvf@198 x@102)
    ($FVF.lookup_Set__contents fvf@194 x@102))))
(assert ($Set.equal ($FVF.domain_Set__contents fvf@198) ($Set.singleton  x@102)))
(set-option :timeout 0)
(push) ; 6
(assert (not (forall (($x Int) ($y Int)) (!
  (implies
    (and
      (and (<= 0 $x) (< $x ($FVF.lookup_Set__max fvf@196 x@102)))
      (and (<= 0 $y) (< $y ($FVF.lookup_Set__max fvf@196 x@102)))
      (=
        ($Seq.index ($FVF.lookup_Set__contents fvf@198 x@102) $x)
        ($Seq.index ($FVF.lookup_Set__contents fvf@198 x@102) $y)))
    (= $x $y))
  :pattern (($Seq.index ($FVF.lookup_Set__contents fvf@198 x@102) $x) ($Seq.index
    ($FVF.lookup_Set__contents fvf@198 x@102)
    $y))))))
(check-sat)
; unsat
(pop) ; 6
; 0.00s
; (get-info :all-statistics)
(declare-fun invOf@199 ($Ref) Int)
(assert (forall (($r $Ref)) (!
  (implies
    (and
      (<= 0 (invOf@199 $r))
      (< (invOf@199 $r) ($FVF.lookup_Set__max fvf@196 x@102)))
    (= ($Seq.index ($FVF.lookup_Set__contents fvf@198 x@102) (invOf@199 $r)) $r))
  :pattern ((invOf@199 $r)))))
(assert (forall ((k@195 Int)) (!
  (implies
    (and (<= 0 k@195) (< k@195 ($FVF.lookup_Set__max fvf@196 x@102)))
    (=
      (invOf@199 ($Seq.index ($FVF.lookup_Set__contents fvf@198 x@102) k@195))
      k@195))
  :pattern (($Seq.index ($FVF.lookup_Set__contents fvf@198 x@102) k@195)))))
(declare-const fvf@200 $FVF<Bool>)
; Precomputing split data for Lookup(Set__contents,fvf@198,x@102)[k@195].Ref__Boolean_value # $k@197
(define-fun $permsTaken12 (($r $Ref)) $Perm
  ($Perm.min
    (ite
      (and
        (<= 0 (invOf@199 $r))
        (< (invOf@199 $r) ($FVF.lookup_Set__max fvf@196 x@102)))
      $k@197
      $Perm.No)
    (ite
      (= $r ($Seq.index ($FVF.lookup_Set__contents fvf@198 x@102) k@195))
      (-
        (ite (= $r ($Seq.index $t@159 i@137)) $Perm.Write $Perm.No)
        ($permsTaken9 $r))
      $Perm.No)))
(define-fun $permsTaken13 (($r $Ref)) $Perm
  ($Perm.min
    (-
      (ite
        (and
          (<= 0 (invOf@199 $r))
          (< (invOf@199 $r) ($FVF.lookup_Set__max fvf@196 x@102)))
        $k@197
        $Perm.No)
      ($permsTaken12 $r))
    (ite
      (= $r ($Seq.index ($FVF.lookup_Set__contents fvf@198 x@102) k@195))
      (-
        (-
          (ite
            (and (<= 0 (invOf@164 $r)) (< (invOf@164 $r) $t@160))
            $Perm.Write
            $Perm.No)
          ($permsTaken7 $r))
        ($permsTaken10 $r))
      $Perm.No)))
(define-fun $permsTaken14 (($r $Ref)) $Perm
  ($Perm.min
    (-
      (-
        (ite
          (and
            (<= 0 (invOf@199 $r))
            (< (invOf@199 $r) ($FVF.lookup_Set__max fvf@196 x@102)))
          $k@197
          $Perm.No)
        ($permsTaken12 $r))
      ($permsTaken13 $r))
    (ite
      (= $r ($Seq.index ($FVF.lookup_Set__contents fvf@198 x@102) k@195))
      (ite (and (<= 0 (invOf@169 $r)) (< (invOf@169 $r) $t@153)) $k@168 $Perm.No)
      $Perm.No)))
; Done precomputing, updating quantified heap chunks
; Constrain original permissions $k@197
(assert (forall (($r $Ref)) (!
  (implies
    (not
      (=
        (-
          (ite (= $r ($Seq.index $t@159 i@137)) $Perm.Write $Perm.No)
          ($permsTaken9 $r))
        $Perm.No))
    (<
      (ite
        (and
          (<= 0 (invOf@199 $r))
          (< (invOf@199 $r) ($FVF.lookup_Set__max fvf@196 x@102)))
        $k@197
        $Perm.No)
      (-
        (ite (= $r ($Seq.index $t@159 i@137)) $Perm.Write $Perm.No)
        ($permsTaken9 $r))))
  :pattern ((invOf@199 $r))
  :pattern ((invOf@199 $r)))))
; Enough permissions taken?
(set-option :timeout 500)
(push) ; 6
(assert (not (=
  (-
    (ite
      (and
        (<=
          0
          (invOf@199 ($Seq.index ($FVF.lookup_Set__contents fvf@198 x@102) k@195)))
        (<
          (invOf@199 ($Seq.index ($FVF.lookup_Set__contents fvf@198 x@102) k@195))
          ($FVF.lookup_Set__max fvf@196 x@102)))
      $k@197
      $Perm.No)
    ($permsTaken12 ($Seq.index ($FVF.lookup_Set__contents fvf@198 x@102) k@195)))
  $Perm.No)))
(check-sat)
; unknown
(pop) ; 6
; 0.01s
; (get-info :all-statistics)
; Constrain original permissions $k@197
(assert (forall (($r $Ref)) (!
  (implies
    (not
      (=
        (-
          (-
            (ite
              (and (<= 0 (invOf@164 $r)) (< (invOf@164 $r) $t@160))
              $Perm.Write
              $Perm.No)
            ($permsTaken7 $r))
          ($permsTaken10 $r))
        $Perm.No))
    (<
      (ite
        (and
          (<= 0 (invOf@199 $r))
          (< (invOf@199 $r) ($FVF.lookup_Set__max fvf@196 x@102)))
        $k@197
        $Perm.No)
      (-
        (-
          (ite
            (and (<= 0 (invOf@164 $r)) (< (invOf@164 $r) $t@160))
            $Perm.Write
            $Perm.No)
          ($permsTaken7 $r))
        ($permsTaken10 $r))))
  :pattern ((invOf@164 $r))
  :pattern ((invOf@164 $r))
  :pattern ((invOf@199 $r))
  :pattern ((invOf@199 $r))
  :pattern ((invOf@164 $r))
  :pattern ((invOf@164 $r)))))
; Enough permissions taken?
(set-option :timeout 500)
(push) ; 6
(assert (not (=
  (-
    (-
      (ite
        (and
          (<=
            0
            (invOf@199 ($Seq.index
              ($FVF.lookup_Set__contents fvf@198 x@102)
              k@195)))
          (<
            (invOf@199 ($Seq.index
              ($FVF.lookup_Set__contents fvf@198 x@102)
              k@195))
            ($FVF.lookup_Set__max fvf@196 x@102)))
        $k@197
        $Perm.No)
      ($permsTaken12 ($Seq.index ($FVF.lookup_Set__contents fvf@198 x@102) k@195)))
    ($permsTaken13 ($Seq.index ($FVF.lookup_Set__contents fvf@198 x@102) k@195)))
  $Perm.No)))
(check-sat)
; unknown
(pop) ; 6
; 0.02s
; (get-info :all-statistics)
; Constrain original permissions $k@197
(assert (forall (($r $Ref)) (!
  (implies
    (not
      (=
        (ite
          (and (<= 0 (invOf@169 $r)) (< (invOf@169 $r) $t@153))
          $k@168
          $Perm.No)
        $Perm.No))
    (ite
      (and (<= 0 (invOf@169 $r)) (< (invOf@169 $r) $t@153))
      (<
        (ite
          (and
            (<= 0 (invOf@199 $r))
            (< (invOf@199 $r) ($FVF.lookup_Set__max fvf@196 x@102)))
          $k@197
          $Perm.No)
        $k@168)
      (<
        (ite
          (and
            (<= 0 (invOf@199 $r))
            (< (invOf@199 $r) ($FVF.lookup_Set__max fvf@196 x@102)))
          $k@197
          $Perm.No)
        $Perm.No)))
  :pattern ((invOf@169 $r))
  :pattern ((invOf@169 $r))
  :pattern ((invOf@169 $r))
  :pattern ((invOf@169 $r))
  :pattern ((invOf@199 $r))
  :pattern ((invOf@199 $r))
  :pattern ((invOf@199 $r))
  :pattern ((invOf@199 $r)))))
; Enough permissions taken?
(set-option :timeout 500)
(push) ; 6
(assert (not (=
  (-
    (-
      (-
        (ite
          (and
            (<=
              0
              (invOf@199 ($Seq.index
                ($FVF.lookup_Set__contents fvf@198 x@102)
                k@195)))
            (<
              (invOf@199 ($Seq.index
                ($FVF.lookup_Set__contents fvf@198 x@102)
                k@195))
              ($FVF.lookup_Set__max fvf@196 x@102)))
          $k@197
          $Perm.No)
        ($permsTaken12 ($Seq.index
          ($FVF.lookup_Set__contents fvf@198 x@102)
          k@195)))
      ($permsTaken13 ($Seq.index ($FVF.lookup_Set__contents fvf@198 x@102) k@195)))
    ($permsTaken14 ($Seq.index ($FVF.lookup_Set__contents fvf@198 x@102) k@195)))
  $Perm.No)))
(check-sat)
; unsat
(pop) ; 6
; 0.01s
; (get-info :all-statistics)
; Final check that enough permissions have been taken
; Done splitting
(assert (forall (($r $Ref)) (!
  (implies
    (and
      (ite
        (and (<= 0 (invOf@169 $r)) (< (invOf@169 $r) $t@153))
        (< $Perm.No $k@168)
        false)
      ($Set.in $r ($FVF.domain_Ref__Boolean_value fvf@200)))
    (=
      ($FVF.lookup_Ref__Boolean_value fvf@200 $r)
      ($FVF.lookup_Ref__Boolean_value $t@147 $r)))
  :pattern (($FVF.lookup_Ref__Boolean_value fvf@200 $r) (invOf@169 $r))
  :pattern (($FVF.lookup_Ref__Boolean_value $t@147 $r) (invOf@169 $r)))))
(assert (forall (($r $Ref)) (!
  (implies
    (and
      (<
        $Perm.No
        (-
          (-
            (ite
              (and (<= 0 (invOf@164 $r)) (< (invOf@164 $r) $t@160))
              $Perm.Write
              $Perm.No)
            ($permsTaken7 $r))
          ($permsTaken10 $r)))
      ($Set.in $r ($FVF.domain_Ref__Boolean_value fvf@200)))
    (=
      ($FVF.lookup_Ref__Boolean_value fvf@200 $r)
      ($FVF.lookup_Ref__Boolean_value $t@156 $r)))
  :pattern (($FVF.lookup_Ref__Boolean_value fvf@200 $r) (invOf@164 $r))
  :pattern (($FVF.lookup_Ref__Boolean_value $t@156 $r) (invOf@164 $r)))))
(assert (forall (($r $Ref)) (!
  (implies
    (and
      (<
        $Perm.No
        (-
          (ite (= $r ($Seq.index $t@159 i@137)) $Perm.Write $Perm.No)
          ($permsTaken9 $r)))
      ($Set.in $r ($FVF.domain_Ref__Boolean_value fvf@200)))
    (=
      ($FVF.lookup_Ref__Boolean_value fvf@200 $r)
      ($FVF.lookup_Ref__Boolean_value fvf@177 $r)))
  :pattern (($FVF.lookup_Ref__Boolean_value fvf@200 $r))
  :pattern (($FVF.lookup_Ref__Boolean_value fvf@177 $r)))))
(assert (forall (($r $Ref)) (!
  (iff
    ($Set.in $r ($FVF.domain_Ref__Boolean_value fvf@200))
    (and
      (<= 0 (invOf@199 $r))
      (< (invOf@199 $r) ($FVF.lookup_Set__max fvf@196 x@102))))
  :pattern (($Set.in $r ($FVF.domain_Ref__Boolean_value fvf@200))))))
; [eval] (0 <= i) && (i <= diz.Set__max)
; [eval] 0 <= i
(push) ; 6
(set-option :timeout 0)
(push) ; 7
(assert (not (not (<= 0 (+ i@137 1)))))
(check-sat)
; unknown
(pop) ; 7
; 0.02s
; (get-info :all-statistics)
(set-option :timeout 0)
(push) ; 7
(assert (not (<= 0 (+ i@137 1))))
(check-sat)
; unsat
(pop) ; 7
; 0.00s
; (get-info :all-statistics)
(push) ; 7
; [then-branch 37] 0 <= i@137 + 1
(assert (<= 0 (+ i@137 1)))
; [eval] i <= diz.Set__max
(pop) ; 7
; [dead else-branch 37] !0 <= i@137 + 1
(pop) ; 6
(set-option :timeout 0)
(push) ; 6
(assert (not (and (<= 0 (+ i@137 1)) (<= (+ i@137 1) $t@160))))
(check-sat)
; unsat
(pop) ; 6
; 0.00s
; (get-info :all-statistics)
(assert (and (<= 0 (+ i@137 1)) (<= (+ i@137 1) $t@160)))
; [eval] (forall k: Int :: (0 <= k) && (k < i) ==> (diz.Set__contents[k].Ref__Boolean_value == diz.Set__contents[k].Ref__Boolean_value && x.Set__contents[k].Ref__Boolean_value))
(declare-const k@201 Int)
(push) ; 6
; [eval] (0 <= k) && (k < i) ==> (diz.Set__contents[k].Ref__Boolean_value == diz.Set__contents[k].Ref__Boolean_value && x.Set__contents[k].Ref__Boolean_value)
; [eval] (0 <= k) && (k < i)
; [eval] 0 <= k
(push) ; 7
(set-option :timeout 0)
(push) ; 8
(assert (not (not (<= 0 k@201))))
(check-sat)
; unknown
(pop) ; 8
; 0.03s
; (get-info :all-statistics)
(set-option :timeout 0)
(push) ; 8
(assert (not (<= 0 k@201)))
(check-sat)
; unknown
(pop) ; 8
; 0.03s
; (get-info :all-statistics)
(push) ; 8
; [then-branch 38] 0 <= k@201
(assert (<= 0 k@201))
; [eval] k < i
(pop) ; 8
(push) ; 8
; [else-branch 38] !0 <= k@201
(assert (not (<= 0 k@201)))
(pop) ; 8
(pop) ; 7
(push) ; 7
(set-option :timeout 0)
(push) ; 8
(assert (not (not (and (<= 0 k@201) (< k@201 (+ i@137 1))))))
(check-sat)
; unknown
(pop) ; 8
; 0.02s
; (get-info :all-statistics)
(set-option :timeout 0)
(push) ; 8
(assert (not (and (<= 0 k@201) (< k@201 (+ i@137 1)))))
(check-sat)
; unknown
(pop) ; 8
; 0.03s
; (get-info :all-statistics)
(push) ; 8
; [then-branch 39] 0 <= k@201 && k@201 < i@137 + 1
(assert (and (<= 0 k@201) (< k@201 (+ i@137 1))))
; [eval] diz.Set__contents[k].Ref__Boolean_value == diz.Set__contents[k].Ref__Boolean_value && x.Set__contents[k].Ref__Boolean_value
; [eval] diz.Set__contents[k]
(set-option :timeout 0)
(push) ; 9
(assert (not (not (= ($Seq.index $t@159 k@201) $Ref.null))))
(check-sat)
; unsat
(pop) ; 9
; 0.00s
; (get-info :all-statistics)
(set-option :timeout 0)
(push) ; 9
(assert (not (<
  $Perm.No
  (+
    (+
      (ite
        (and
          (<= 0 (invOf@169 ($Seq.index $t@159 k@201)))
          (< (invOf@169 ($Seq.index $t@159 k@201)) $t@153))
        $k@168
        $Perm.No)
      (-
        (ite
          (and
            (<= 0 (invOf@164 ($Seq.index $t@159 k@201)))
            (< (invOf@164 ($Seq.index $t@159 k@201)) $t@160))
          $Perm.Write
          $Perm.No)
        ($permsTaken7 ($Seq.index $t@159 k@201))))
    (ite
      (= ($Seq.index $t@159 k@201) ($Seq.index $t@159 i@137))
      $Perm.Write
      $Perm.No)))))
(check-sat)
; unsat
(pop) ; 9
; 0.01s
; (get-info :all-statistics)
(declare-const fvf@202 $FVF<Bool>)
(assert (forall (($r $Ref)) (!
  (implies
    (and
      (ite
        (and (<= 0 (invOf@169 $r)) (< (invOf@169 $r) $t@153))
        (< $Perm.No $k@168)
        false)
      ($Set.in $r ($FVF.domain_Ref__Boolean_value fvf@202)))
    (=
      ($FVF.lookup_Ref__Boolean_value fvf@202 $r)
      ($FVF.lookup_Ref__Boolean_value $t@147 $r)))
  :pattern (($FVF.lookup_Ref__Boolean_value fvf@202 $r) (invOf@169 $r))
  :pattern (($FVF.lookup_Ref__Boolean_value $t@147 $r) (invOf@169 $r)))))
(assert (forall (($r $Ref)) (!
  (implies
    (and
      (<
        $Perm.No
        (-
          (ite
            (and (<= 0 (invOf@164 $r)) (< (invOf@164 $r) $t@160))
            $Perm.Write
            $Perm.No)
          ($permsTaken7 $r)))
      ($Set.in $r ($FVF.domain_Ref__Boolean_value fvf@202)))
    (=
      ($FVF.lookup_Ref__Boolean_value fvf@202 $r)
      ($FVF.lookup_Ref__Boolean_value $t@156 $r)))
  :pattern (($FVF.lookup_Ref__Boolean_value fvf@202 $r) (invOf@164 $r))
  :pattern (($FVF.lookup_Ref__Boolean_value $t@156 $r) (invOf@164 $r)))))
(assert (forall (($r $Ref)) (!
  (implies
    (and
      (= $r ($Seq.index $t@159 i@137))
      ($Set.in $r ($FVF.domain_Ref__Boolean_value fvf@202)))
    (=
      ($FVF.lookup_Ref__Boolean_value fvf@202 $r)
      ($FVF.lookup_Ref__Boolean_value fvf@177 $r)))
  :pattern (($FVF.lookup_Ref__Boolean_value fvf@202 $r))
  :pattern (($FVF.lookup_Ref__Boolean_value fvf@177 $r)))))
(assert (forall ((k@201 Int)) (!
  (iff
    ($Set.in ($Seq.index $t@159 k@201) ($FVF.domain_Ref__Boolean_value fvf@202))
    (and (and (<= 0 k@201) (< k@201 (+ i@137 1))) (<= $t@116 $t@123)))
  :pattern (($Set.in
    ($Seq.index $t@159 k@201)
    ($FVF.domain_Ref__Boolean_value fvf@202))))))
; [eval] diz.Set__contents[k].Ref__Boolean_value && x.Set__contents[k].Ref__Boolean_value
; [eval] diz.Set__contents[k]
(set-option :timeout 0)
(push) ; 9
(assert (not (not (= ($Seq.index $t@159 k@201) $Ref.null))))
(check-sat)
; unsat
(pop) ; 9
; 0.00s
; (get-info :all-statistics)
(set-option :timeout 0)
(push) ; 9
(assert (not (<
  $Perm.No
  (+
    (+
      (ite
        (and
          (<= 0 (invOf@169 ($Seq.index $t@159 k@201)))
          (< (invOf@169 ($Seq.index $t@159 k@201)) $t@153))
        $k@168
        $Perm.No)
      (-
        (ite
          (and
            (<= 0 (invOf@164 ($Seq.index $t@159 k@201)))
            (< (invOf@164 ($Seq.index $t@159 k@201)) $t@160))
          $Perm.Write
          $Perm.No)
        ($permsTaken7 ($Seq.index $t@159 k@201))))
    (ite
      (= ($Seq.index $t@159 k@201) ($Seq.index $t@159 i@137))
      $Perm.Write
      $Perm.No)))))
(check-sat)
; unsat
(pop) ; 9
; 0.01s
; (get-info :all-statistics)
(declare-const fvf@203 $FVF<Bool>)
(push) ; 9
(set-option :timeout 0)
(push) ; 10
(assert (not (not ($FVF.lookup_Ref__Boolean_value fvf@202 ($Seq.index $t@159 k@201)))))
(check-sat)
; unknown
(pop) ; 10
; 0.09s
; (get-info :all-statistics)
(set-option :timeout 0)
(push) ; 10
(assert (not ($FVF.lookup_Ref__Boolean_value fvf@202 ($Seq.index $t@159 k@201))))
(check-sat)
; unknown
(pop) ; 10
; 0.07s
; (get-info :all-statistics)
(push) ; 10
; [then-branch 40] Lookup(Ref__Boolean_value,fvf@202,$t@159[k@201])
(assert ($FVF.lookup_Ref__Boolean_value fvf@202 ($Seq.index $t@159 k@201)))
; [eval] x.Set__contents[k]
(set-option :timeout 0)
(push) ; 11
(assert (not (not (= ($Seq.index $t@150 k@201) $Ref.null))))
(check-sat)
; unsat
(pop) ; 11
; 0.00s
; (get-info :all-statistics)
(set-option :timeout 0)
(push) ; 11
(assert (not (<
  $Perm.No
  (+
    (+
      (ite
        (and
          (<= 0 (invOf@169 ($Seq.index $t@150 k@201)))
          (< (invOf@169 ($Seq.index $t@150 k@201)) $t@153))
        $k@168
        $Perm.No)
      (-
        (ite
          (and
            (<= 0 (invOf@164 ($Seq.index $t@150 k@201)))
            (< (invOf@164 ($Seq.index $t@150 k@201)) $t@160))
          $Perm.Write
          $Perm.No)
        ($permsTaken7 ($Seq.index $t@150 k@201))))
    (ite
      (= ($Seq.index $t@150 k@201) ($Seq.index $t@159 i@137))
      $Perm.Write
      $Perm.No)))))
(check-sat)
; unsat
(pop) ; 11
; 0.02s
; (get-info :all-statistics)
(declare-const fvf@204 $FVF<Bool>)
(assert (forall (($r $Ref)) (!
  (implies
    (and
      (ite
        (and (<= 0 (invOf@169 $r)) (< (invOf@169 $r) $t@153))
        (< $Perm.No $k@168)
        false)
      ($Set.in $r ($FVF.domain_Ref__Boolean_value fvf@204)))
    (=
      ($FVF.lookup_Ref__Boolean_value fvf@204 $r)
      ($FVF.lookup_Ref__Boolean_value $t@147 $r)))
  :pattern (($FVF.lookup_Ref__Boolean_value fvf@204 $r) (invOf@169 $r))
  :pattern (($FVF.lookup_Ref__Boolean_value $t@147 $r) (invOf@169 $r)))))
(assert (forall (($r $Ref)) (!
  (implies
    (and
      (<
        $Perm.No
        (-
          (ite
            (and (<= 0 (invOf@164 $r)) (< (invOf@164 $r) $t@160))
            $Perm.Write
            $Perm.No)
          ($permsTaken7 $r)))
      ($Set.in $r ($FVF.domain_Ref__Boolean_value fvf@204)))
    (=
      ($FVF.lookup_Ref__Boolean_value fvf@204 $r)
      ($FVF.lookup_Ref__Boolean_value $t@156 $r)))
  :pattern (($FVF.lookup_Ref__Boolean_value fvf@204 $r) (invOf@164 $r))
  :pattern (($FVF.lookup_Ref__Boolean_value $t@156 $r) (invOf@164 $r)))))
(assert (forall (($r $Ref)) (!
  (implies
    (and
      (= $r ($Seq.index $t@159 i@137))
      ($Set.in $r ($FVF.domain_Ref__Boolean_value fvf@204)))
    (=
      ($FVF.lookup_Ref__Boolean_value fvf@204 $r)
      ($FVF.lookup_Ref__Boolean_value fvf@177 $r)))
  :pattern (($FVF.lookup_Ref__Boolean_value fvf@204 $r))
  :pattern (($FVF.lookup_Ref__Boolean_value fvf@177 $r)))))
(assert (forall ((k@201 Int)) (!
  (iff
    ($Set.in ($Seq.index $t@150 k@201) ($FVF.domain_Ref__Boolean_value fvf@204))
    (and
      ($FVF.lookup_Ref__Boolean_value fvf@202 ($Seq.index $t@159 k@201))
      (and (<= 0 k@201) (< k@201 (+ i@137 1)))
      (<= $t@116 $t@123)))
  :pattern (($Set.in
    ($Seq.index $t@150 k@201)
    ($FVF.domain_Ref__Boolean_value fvf@204))))))
(pop) ; 10
(push) ; 10
; [else-branch 40] !Lookup(Ref__Boolean_value,fvf@202,$t@159[k@201])
(assert (not ($FVF.lookup_Ref__Boolean_value fvf@202 ($Seq.index $t@159 k@201))))
(pop) ; 10
(pop) ; 9
(assert (forall ((k@201 Int)) (!
  (iff
    ($Set.in ($Seq.index $t@150 k@201) ($FVF.domain_Ref__Boolean_value fvf@204))
    (and
      ($FVF.lookup_Ref__Boolean_value fvf@202 ($Seq.index $t@159 k@201))
      (and (<= 0 k@201) (< k@201 (+ i@137 1)))
      (<= $t@116 $t@123)))
  :pattern (($Set.in
    ($Seq.index $t@150 k@201)
    ($FVF.domain_Ref__Boolean_value fvf@204))))))
(assert (forall (($r $Ref)) (!
  (implies
    (and
      (= $r ($Seq.index $t@159 i@137))
      ($Set.in $r ($FVF.domain_Ref__Boolean_value fvf@204)))
    (=
      ($FVF.lookup_Ref__Boolean_value fvf@204 $r)
      ($FVF.lookup_Ref__Boolean_value fvf@177 $r)))
  :pattern (($FVF.lookup_Ref__Boolean_value fvf@204 $r))
  :pattern (($FVF.lookup_Ref__Boolean_value fvf@177 $r)))))
(assert (forall (($r $Ref)) (!
  (implies
    (and
      (<
        $Perm.No
        (-
          (ite
            (and (<= 0 (invOf@164 $r)) (< (invOf@164 $r) $t@160))
            $Perm.Write
            $Perm.No)
          ($permsTaken7 $r)))
      ($Set.in $r ($FVF.domain_Ref__Boolean_value fvf@204)))
    (=
      ($FVF.lookup_Ref__Boolean_value fvf@204 $r)
      ($FVF.lookup_Ref__Boolean_value $t@156 $r)))
  :pattern (($FVF.lookup_Ref__Boolean_value fvf@204 $r) (invOf@164 $r))
  :pattern (($FVF.lookup_Ref__Boolean_value $t@156 $r) (invOf@164 $r)))))
(assert (forall (($r $Ref)) (!
  (implies
    (and
      (ite
        (and (<= 0 (invOf@169 $r)) (< (invOf@169 $r) $t@153))
        (< $Perm.No $k@168)
        false)
      ($Set.in $r ($FVF.domain_Ref__Boolean_value fvf@204)))
    (=
      ($FVF.lookup_Ref__Boolean_value fvf@204 $r)
      ($FVF.lookup_Ref__Boolean_value $t@147 $r)))
  :pattern (($FVF.lookup_Ref__Boolean_value fvf@204 $r) (invOf@169 $r))
  :pattern (($FVF.lookup_Ref__Boolean_value $t@147 $r) (invOf@169 $r)))))
(pop) ; 8
(push) ; 8
; [else-branch 39] !0 <= k@201 && k@201 < i@137 + 1
(assert (not (and (<= 0 k@201) (< k@201 (+ i@137 1)))))
(pop) ; 8
(pop) ; 7
(assert (forall (($r $Ref)) (!
  (implies
    (and
      (ite
        (and (<= 0 (invOf@169 $r)) (< (invOf@169 $r) $t@153))
        (< $Perm.No $k@168)
        false)
      ($Set.in $r ($FVF.domain_Ref__Boolean_value fvf@204)))
    (=
      ($FVF.lookup_Ref__Boolean_value fvf@204 $r)
      ($FVF.lookup_Ref__Boolean_value $t@147 $r)))
  :pattern (($FVF.lookup_Ref__Boolean_value fvf@204 $r) (invOf@169 $r))
  :pattern (($FVF.lookup_Ref__Boolean_value $t@147 $r) (invOf@169 $r)))))
(assert (forall (($r $Ref)) (!
  (implies
    (and
      (<
        $Perm.No
        (-
          (ite
            (and (<= 0 (invOf@164 $r)) (< (invOf@164 $r) $t@160))
            $Perm.Write
            $Perm.No)
          ($permsTaken7 $r)))
      ($Set.in $r ($FVF.domain_Ref__Boolean_value fvf@204)))
    (=
      ($FVF.lookup_Ref__Boolean_value fvf@204 $r)
      ($FVF.lookup_Ref__Boolean_value $t@156 $r)))
  :pattern (($FVF.lookup_Ref__Boolean_value fvf@204 $r) (invOf@164 $r))
  :pattern (($FVF.lookup_Ref__Boolean_value $t@156 $r) (invOf@164 $r)))))
(assert (forall (($r $Ref)) (!
  (implies
    (and
      (= $r ($Seq.index $t@159 i@137))
      ($Set.in $r ($FVF.domain_Ref__Boolean_value fvf@204)))
    (=
      ($FVF.lookup_Ref__Boolean_value fvf@204 $r)
      ($FVF.lookup_Ref__Boolean_value fvf@177 $r)))
  :pattern (($FVF.lookup_Ref__Boolean_value fvf@204 $r))
  :pattern (($FVF.lookup_Ref__Boolean_value fvf@177 $r)))))
(assert (forall ((k@201 Int)) (!
  (iff
    ($Set.in ($Seq.index $t@150 k@201) ($FVF.domain_Ref__Boolean_value fvf@204))
    (and
      ($FVF.lookup_Ref__Boolean_value fvf@202 ($Seq.index $t@159 k@201))
      (and (<= 0 k@201) (< k@201 (+ i@137 1)))
      (<= $t@116 $t@123)))
  :pattern (($Set.in
    ($Seq.index $t@150 k@201)
    ($FVF.domain_Ref__Boolean_value fvf@204))))))
(assert (forall ((k@201 Int)) (!
  (iff
    ($Set.in ($Seq.index $t@159 k@201) ($FVF.domain_Ref__Boolean_value fvf@202))
    (and (and (<= 0 k@201) (< k@201 (+ i@137 1))) (<= $t@116 $t@123)))
  :pattern (($Set.in
    ($Seq.index $t@159 k@201)
    ($FVF.domain_Ref__Boolean_value fvf@202))))))
(assert (forall (($r $Ref)) (!
  (implies
    (and
      (= $r ($Seq.index $t@159 i@137))
      ($Set.in $r ($FVF.domain_Ref__Boolean_value fvf@202)))
    (=
      ($FVF.lookup_Ref__Boolean_value fvf@202 $r)
      ($FVF.lookup_Ref__Boolean_value fvf@177 $r)))
  :pattern (($FVF.lookup_Ref__Boolean_value fvf@202 $r))
  :pattern (($FVF.lookup_Ref__Boolean_value fvf@177 $r)))))
(assert (forall (($r $Ref)) (!
  (implies
    (and
      (<
        $Perm.No
        (-
          (ite
            (and (<= 0 (invOf@164 $r)) (< (invOf@164 $r) $t@160))
            $Perm.Write
            $Perm.No)
          ($permsTaken7 $r)))
      ($Set.in $r ($FVF.domain_Ref__Boolean_value fvf@202)))
    (=
      ($FVF.lookup_Ref__Boolean_value fvf@202 $r)
      ($FVF.lookup_Ref__Boolean_value $t@156 $r)))
  :pattern (($FVF.lookup_Ref__Boolean_value fvf@202 $r) (invOf@164 $r))
  :pattern (($FVF.lookup_Ref__Boolean_value $t@156 $r) (invOf@164 $r)))))
(assert (forall (($r $Ref)) (!
  (implies
    (and
      (ite
        (and (<= 0 (invOf@169 $r)) (< (invOf@169 $r) $t@153))
        (< $Perm.No $k@168)
        false)
      ($Set.in $r ($FVF.domain_Ref__Boolean_value fvf@202)))
    (=
      ($FVF.lookup_Ref__Boolean_value fvf@202 $r)
      ($FVF.lookup_Ref__Boolean_value $t@147 $r)))
  :pattern (($FVF.lookup_Ref__Boolean_value fvf@202 $r) (invOf@169 $r))
  :pattern (($FVF.lookup_Ref__Boolean_value $t@147 $r) (invOf@169 $r)))))
(pop) ; 6
(assert (forall (($r $Ref)) (!
  (implies
    (and
      (ite
        (and (<= 0 (invOf@169 $r)) (< (invOf@169 $r) $t@153))
        (< $Perm.No $k@168)
        false)
      ($Set.in $r ($FVF.domain_Ref__Boolean_value fvf@204)))
    (=
      ($FVF.lookup_Ref__Boolean_value fvf@204 $r)
      ($FVF.lookup_Ref__Boolean_value $t@147 $r)))
  :pattern (($FVF.lookup_Ref__Boolean_value fvf@204 $r) (invOf@169 $r))
  :pattern (($FVF.lookup_Ref__Boolean_value $t@147 $r) (invOf@169 $r)))))
(assert (forall (($r $Ref)) (!
  (implies
    (and
      (<
        $Perm.No
        (-
          (ite
            (and (<= 0 (invOf@164 $r)) (< (invOf@164 $r) $t@160))
            $Perm.Write
            $Perm.No)
          ($permsTaken7 $r)))
      ($Set.in $r ($FVF.domain_Ref__Boolean_value fvf@204)))
    (=
      ($FVF.lookup_Ref__Boolean_value fvf@204 $r)
      ($FVF.lookup_Ref__Boolean_value $t@156 $r)))
  :pattern (($FVF.lookup_Ref__Boolean_value fvf@204 $r) (invOf@164 $r))
  :pattern (($FVF.lookup_Ref__Boolean_value $t@156 $r) (invOf@164 $r)))))
(assert (forall (($r $Ref)) (!
  (implies
    (and
      (= $r ($Seq.index $t@159 i@137))
      ($Set.in $r ($FVF.domain_Ref__Boolean_value fvf@204)))
    (=
      ($FVF.lookup_Ref__Boolean_value fvf@204 $r)
      ($FVF.lookup_Ref__Boolean_value fvf@177 $r)))
  :pattern (($FVF.lookup_Ref__Boolean_value fvf@204 $r))
  :pattern (($FVF.lookup_Ref__Boolean_value fvf@177 $r)))))
(assert (forall ((k@201 Int)) (!
  (iff
    ($Set.in ($Seq.index $t@150 k@201) ($FVF.domain_Ref__Boolean_value fvf@204))
    (and
      ($FVF.lookup_Ref__Boolean_value fvf@202 ($Seq.index $t@159 k@201))
      (and (<= 0 k@201) (< k@201 (+ i@137 1)))
      (<= $t@116 $t@123)))
  :pattern (($Set.in
    ($Seq.index $t@150 k@201)
    ($FVF.domain_Ref__Boolean_value fvf@204))))))
(assert (forall ((k@201 Int)) (!
  (iff
    ($Set.in ($Seq.index $t@159 k@201) ($FVF.domain_Ref__Boolean_value fvf@202))
    (and (and (<= 0 k@201) (< k@201 (+ i@137 1))) (<= $t@116 $t@123)))
  :pattern (($Set.in
    ($Seq.index $t@159 k@201)
    ($FVF.domain_Ref__Boolean_value fvf@202))))))
(assert (forall (($r $Ref)) (!
  (implies
    (and
      (= $r ($Seq.index $t@159 i@137))
      ($Set.in $r ($FVF.domain_Ref__Boolean_value fvf@202)))
    (=
      ($FVF.lookup_Ref__Boolean_value fvf@202 $r)
      ($FVF.lookup_Ref__Boolean_value fvf@177 $r)))
  :pattern (($FVF.lookup_Ref__Boolean_value fvf@202 $r))
  :pattern (($FVF.lookup_Ref__Boolean_value fvf@177 $r)))))
(assert (forall (($r $Ref)) (!
  (implies
    (and
      (<
        $Perm.No
        (-
          (ite
            (and (<= 0 (invOf@164 $r)) (< (invOf@164 $r) $t@160))
            $Perm.Write
            $Perm.No)
          ($permsTaken7 $r)))
      ($Set.in $r ($FVF.domain_Ref__Boolean_value fvf@202)))
    (=
      ($FVF.lookup_Ref__Boolean_value fvf@202 $r)
      ($FVF.lookup_Ref__Boolean_value $t@156 $r)))
  :pattern (($FVF.lookup_Ref__Boolean_value fvf@202 $r) (invOf@164 $r))
  :pattern (($FVF.lookup_Ref__Boolean_value $t@156 $r) (invOf@164 $r)))))
(assert (forall (($r $Ref)) (!
  (implies
    (and
      (ite
        (and (<= 0 (invOf@169 $r)) (< (invOf@169 $r) $t@153))
        (< $Perm.No $k@168)
        false)
      ($Set.in $r ($FVF.domain_Ref__Boolean_value fvf@202)))
    (=
      ($FVF.lookup_Ref__Boolean_value fvf@202 $r)
      ($FVF.lookup_Ref__Boolean_value $t@147 $r)))
  :pattern (($FVF.lookup_Ref__Boolean_value fvf@202 $r) (invOf@169 $r))
  :pattern (($FVF.lookup_Ref__Boolean_value $t@147 $r) (invOf@169 $r)))))
(set-option :timeout 0)
(push) ; 6
(assert (not (forall ((k@201 Int)) (!
  (implies
    (and (<= 0 k@201) (< k@201 (+ i@137 1)))
    (=
      ($FVF.lookup_Ref__Boolean_value fvf@202 ($Seq.index $t@159 k@201))
      (and
        ($FVF.lookup_Ref__Boolean_value fvf@202 ($Seq.index $t@159 k@201))
        ($FVF.lookup_Ref__Boolean_value fvf@204 ($Seq.index $t@150 k@201)))))
  :pattern (($Seq.index $t@159 k@201))
  :pattern (($Seq.index $t@159 k@201))
  :pattern (($Seq.index $t@150 k@201))))))
(check-sat)
; unsat
(pop) ; 6
; 0.04s
; (get-info :all-statistics)
(assert (forall ((k@201 Int)) (!
  (implies
    (and (<= 0 k@201) (< k@201 (+ i@137 1)))
    (=
      ($FVF.lookup_Ref__Boolean_value fvf@202 ($Seq.index $t@159 k@201))
      (and
        ($FVF.lookup_Ref__Boolean_value fvf@202 ($Seq.index $t@159 k@201))
        ($FVF.lookup_Ref__Boolean_value fvf@204 ($Seq.index $t@150 k@201)))))
  :pattern (($Seq.index $t@159 k@201))
  :pattern (($Seq.index $t@159 k@201))
  :pattern (($Seq.index $t@150 k@201)))))
(pop) ; 5
(push) ; 5
; Establish loop invariant
(declare-const $k@205 $Perm)
(assert ($Perm.isValidVar $k@205))
(assert ($Perm.isReadVar $k@205 $Perm.Write))
(set-option :timeout 0)
(push) ; 6
(assert (not (or (= $k@205 $Perm.No) true)))
(check-sat)
; unsat
(pop) ; 6
; 0.00s
; (get-info :all-statistics)
(assert (< $k@205 $k@115))
; [eval] diz.Set__max > 0
(declare-const $k@206 $Perm)
(assert ($Perm.isValidVar $k@206))
(assert ($Perm.isReadVar $k@206 $Perm.Write))
(set-option :timeout 0)
(push) ; 6
(assert (not (or (= $k@206 $Perm.No) true)))
(check-sat)
; unsat
(pop) ; 6
; 0.00s
; (get-info :all-statistics)
(assert (< $k@206 $k@117))
; [eval] |diz.Set__contents| == diz.Set__max
; [eval] |diz.Set__contents|
(declare-const fvf@207 $FVF<Int>)
(declare-const fvf@208 $FVF<Int>)
(declare-const fvf@209 $FVF<$Seq<$Ref>>)
(declare-const fvf@210 $FVF<$Seq<$Ref>>)
(assert (= ($FVF.lookup_Set__max fvf@207 diz@101) $t@116))
(assert ($Set.equal ($FVF.domain_Set__max fvf@207) ($Set.singleton  diz@101)))
(assert (= ($FVF.lookup_Set__max fvf@208 x@102) $t@123))
(assert ($Set.equal ($FVF.domain_Set__max fvf@208) ($Set.singleton  x@102)))
(assert ($Seq.equal ($FVF.lookup_Set__contents fvf@209 diz@101) $t@118))
(assert ($Set.equal ($FVF.domain_Set__contents fvf@209) ($Set.singleton  diz@101)))
(assert ($Seq.equal ($FVF.lookup_Set__contents fvf@210 x@102) $t@125))
(assert ($Set.equal ($FVF.domain_Set__contents fvf@210) ($Set.singleton  x@102)))
(declare-const k@211 Int)
; [eval] (0 <= k) && (k < diz.Set__max)
; [eval] 0 <= k
(push) ; 6
(set-option :timeout 0)
(push) ; 7
(assert (not (not (<= 0 k@211))))
(check-sat)
; unknown
(pop) ; 7
; 0.00s
; (get-info :all-statistics)
(set-option :timeout 0)
(push) ; 7
(assert (not (<= 0 k@211)))
(check-sat)
; unknown
(pop) ; 7
; 0.00s
; (get-info :all-statistics)
(push) ; 7
; [then-branch 41] 0 <= k@211
(assert (<= 0 k@211))
; [eval] k < diz.Set__max
(set-option :timeout 0)
(push) ; 8
(assert (not (< $Perm.No (+ $k@115 (ite (= diz@101 x@102) $k@122 $Perm.No)))))
(check-sat)
; unsat
(pop) ; 8
; 0.00s
; (get-info :all-statistics)
(declare-const fvf@212 $FVF<Int>)
(assert (implies
  (< $Perm.No $k@115)
  (=
    ($FVF.lookup_Set__max fvf@212 diz@101)
    ($FVF.lookup_Set__max fvf@207 diz@101))))
(assert (implies
  (ite (= diz@101 x@102) (< $Perm.No $k@122) false)
  (=
    ($FVF.lookup_Set__max fvf@212 diz@101)
    ($FVF.lookup_Set__max fvf@208 diz@101))))
(assert ($Set.equal ($FVF.domain_Set__max fvf@212) ($Set.singleton  diz@101)))
(pop) ; 7
(push) ; 7
; [else-branch 41] !0 <= k@211
(assert (not (<= 0 k@211)))
(pop) ; 7
(pop) ; 6
(assert ($Set.equal ($FVF.domain_Set__max fvf@212) ($Set.singleton  diz@101)))
(assert (implies
  (ite (= diz@101 x@102) (< $Perm.No $k@122) false)
  (=
    ($FVF.lookup_Set__max fvf@212 diz@101)
    ($FVF.lookup_Set__max fvf@208 diz@101))))
(assert (implies
  (< $Perm.No $k@115)
  (=
    ($FVF.lookup_Set__max fvf@212 diz@101)
    ($FVF.lookup_Set__max fvf@207 diz@101))))
(set-option :timeout 0)
(push) ; 6
(assert (not (not (and (<= 0 k@211) (< k@211 ($FVF.lookup_Set__max fvf@212 diz@101))))))
(check-sat)
; unknown
(pop) ; 6
; 0.00s
; (get-info :all-statistics)
(assert (and (<= 0 k@211) (< k@211 ($FVF.lookup_Set__max fvf@212 diz@101))))
; [eval] diz.Set__contents[k]
(set-option :timeout 0)
(push) ; 6
(assert (not (< $Perm.No (+ $k@117 (ite (= diz@101 x@102) $k@124 $Perm.No)))))
(check-sat)
; unsat
(pop) ; 6
; 0.00s
; (get-info :all-statistics)
(declare-const fvf@213 $FVF<$Seq<$Ref>>)
(assert (implies
  (< $Perm.No $k@117)
  ($Seq.equal
    ($FVF.lookup_Set__contents fvf@213 diz@101)
    ($FVF.lookup_Set__contents fvf@209 diz@101))))
(assert (implies
  (ite (= diz@101 x@102) (< $Perm.No $k@124) false)
  ($Seq.equal
    ($FVF.lookup_Set__contents fvf@213 diz@101)
    ($FVF.lookup_Set__contents fvf@210 diz@101))))
(assert ($Set.equal ($FVF.domain_Set__contents fvf@213) ($Set.singleton  diz@101)))
(set-option :timeout 0)
(push) ; 6
(assert (not (forall (($x Int) ($y Int)) (!
  (implies
    (and
      (and (<= 0 $x) (< $x ($FVF.lookup_Set__max fvf@212 diz@101)))
      (and (<= 0 $y) (< $y ($FVF.lookup_Set__max fvf@212 diz@101)))
      (=
        ($Seq.index ($FVF.lookup_Set__contents fvf@213 diz@101) $x)
        ($Seq.index ($FVF.lookup_Set__contents fvf@213 diz@101) $y)))
    (= $x $y))
  :pattern (($Seq.index ($FVF.lookup_Set__contents fvf@213 diz@101) $x) ($Seq.index
    ($FVF.lookup_Set__contents fvf@213 diz@101)
    $y))))))
(check-sat)
; unsat
(pop) ; 6
; 0.00s
; (get-info :all-statistics)
(declare-fun invOf@214 ($Ref) Int)
(assert (forall (($r $Ref)) (!
  (implies
    (and
      (<= 0 (invOf@214 $r))
      (< (invOf@214 $r) ($FVF.lookup_Set__max fvf@212 diz@101)))
    (=
      ($Seq.index ($FVF.lookup_Set__contents fvf@213 diz@101) (invOf@214 $r))
      $r))
  :pattern ((invOf@214 $r)))))
(assert (forall ((k@211 Int)) (!
  (implies
    (and (<= 0 k@211) (< k@211 ($FVF.lookup_Set__max fvf@212 diz@101)))
    (=
      (invOf@214 ($Seq.index ($FVF.lookup_Set__contents fvf@213 diz@101) k@211))
      k@211))
  :pattern (($Seq.index ($FVF.lookup_Set__contents fvf@213 diz@101) k@211)))))
(declare-const fvf@215 $FVF<Bool>)
; Precomputing split data for Lookup(Set__contents,fvf@213,diz@101)[k@211].Ref__Boolean_value # W
(define-fun $permsTaken15 (($r $Ref)) $Perm
  ($Perm.min
    (ite
      (and
        (<= 0 (invOf@214 $r))
        (< (invOf@214 $r) ($FVF.lookup_Set__max fvf@212 diz@101)))
      $Perm.Write
      $Perm.No)
    (ite
      (= $r ($Seq.index ($FVF.lookup_Set__contents fvf@213 diz@101) k@211))
      (ite (and (<= 0 (invOf@129 $r)) (< (invOf@129 $r) $t@123)) $k@127 $Perm.No)
      $Perm.No)))
(define-fun $permsTaken16 (($r $Ref)) $Perm
  ($Perm.min
    (-
      (ite
        (and
          (<= 0 (invOf@214 $r))
          (< (invOf@214 $r) ($FVF.lookup_Set__max fvf@212 diz@101)))
        $Perm.Write
        $Perm.No)
      ($permsTaken15 $r))
    (ite
      (= $r ($Seq.index ($FVF.lookup_Set__contents fvf@213 diz@101) k@211))
      (ite
        (and (<= 0 (invOf@121 $r)) (< (invOf@121 $r) $t@116))
        $Perm.Write
        $Perm.No)
      $Perm.No)))
; Done precomputing, updating quantified heap chunks
; Chunk depleted?
(set-option :timeout 500)
(push) ; 6
(assert (not (forall (($r $Ref)) (!
  (=
    (-
      (ite (and (<= 0 (invOf@129 $r)) (< (invOf@129 $r) $t@123)) $k@127 $Perm.No)
      ($permsTaken15 $r))
    $Perm.No)
  ))))
(check-sat)
; unknown
(pop) ; 6
; 0.00s
; (get-info :all-statistics)
; Enough permissions taken?
(set-option :timeout 500)
(push) ; 6
(assert (not (=
  (-
    (ite
      (and
        (<=
          0
          (invOf@214 ($Seq.index
            ($FVF.lookup_Set__contents fvf@213 diz@101)
            k@211)))
        (<
          (invOf@214 ($Seq.index
            ($FVF.lookup_Set__contents fvf@213 diz@101)
            k@211))
          ($FVF.lookup_Set__max fvf@212 diz@101)))
      $Perm.Write
      $Perm.No)
    ($permsTaken15 ($Seq.index ($FVF.lookup_Set__contents fvf@213 diz@101) k@211)))
  $Perm.No)))
(check-sat)
; unknown
(pop) ; 6
; 0.00s
; (get-info :all-statistics)
; Chunk depleted?
(set-option :timeout 500)
(push) ; 6
(assert (not (forall (($r $Ref)) (!
  (=
    (-
      (ite
        (and (<= 0 (invOf@121 $r)) (< (invOf@121 $r) $t@116))
        $Perm.Write
        $Perm.No)
      ($permsTaken16 $r))
    $Perm.No)
  ))))
(check-sat)
; unknown
(pop) ; 6
; 0.00s
; (get-info :all-statistics)
; Enough permissions taken?
(set-option :timeout 500)
(push) ; 6
(assert (not (=
  (-
    (-
      (ite
        (and
          (<=
            0
            (invOf@214 ($Seq.index
              ($FVF.lookup_Set__contents fvf@213 diz@101)
              k@211)))
          (<
            (invOf@214 ($Seq.index
              ($FVF.lookup_Set__contents fvf@213 diz@101)
              k@211))
            ($FVF.lookup_Set__max fvf@212 diz@101)))
        $Perm.Write
        $Perm.No)
      ($permsTaken15 ($Seq.index
        ($FVF.lookup_Set__contents fvf@213 diz@101)
        k@211)))
    ($permsTaken16 ($Seq.index ($FVF.lookup_Set__contents fvf@213 diz@101) k@211)))
  $Perm.No)))
(check-sat)
; unsat
(pop) ; 6
; 0.00s
; (get-info :all-statistics)
; Final check that enough permissions have been taken
; Done splitting
(assert (forall (($r $Ref)) (!
  (implies
    (and
      (and (<= 0 (invOf@121 $r)) (< (invOf@121 $r) $t@116))
      ($Set.in $r ($FVF.domain_Ref__Boolean_value fvf@215)))
    (=
      ($FVF.lookup_Ref__Boolean_value fvf@215 $r)
      ($FVF.lookup_Ref__Boolean_value $t@120 $r)))
  :pattern (($FVF.lookup_Ref__Boolean_value fvf@215 $r) (invOf@121 $r))
  :pattern (($FVF.lookup_Ref__Boolean_value $t@120 $r) (invOf@121 $r)))))
(assert (forall (($r $Ref)) (!
  (implies
    (and
      (ite
        (and (<= 0 (invOf@129 $r)) (< (invOf@129 $r) $t@123))
        (< $Perm.No $k@127)
        false)
      ($Set.in $r ($FVF.domain_Ref__Boolean_value fvf@215)))
    (=
      ($FVF.lookup_Ref__Boolean_value fvf@215 $r)
      ($FVF.lookup_Ref__Boolean_value $t@128 $r)))
  :pattern (($FVF.lookup_Ref__Boolean_value fvf@215 $r) (invOf@129 $r))
  :pattern (($FVF.lookup_Ref__Boolean_value $t@128 $r) (invOf@129 $r)))))
(assert (forall (($r $Ref)) (!
  (iff
    ($Set.in $r ($FVF.domain_Ref__Boolean_value fvf@215))
    (and
      (<= 0 (invOf@214 $r))
      (< (invOf@214 $r) ($FVF.lookup_Set__max fvf@212 diz@101))))
  :pattern (($Set.in $r ($FVF.domain_Ref__Boolean_value fvf@215))))))
; [eval] x != null
(declare-const $k@216 $Perm)
(assert ($Perm.isValidVar $k@216))
(assert ($Perm.isReadVar $k@216 $Perm.Write))
(set-option :timeout 0)
(push) ; 6
(assert (not (or (= $k@216 $Perm.No) true)))
(check-sat)
; unsat
(pop) ; 6
; 0.00s
; (get-info :all-statistics)
(assert (< $k@216 $k@122))
; [eval] x.Set__max > 0
(declare-const $k@217 $Perm)
(assert ($Perm.isValidVar $k@217))
(assert ($Perm.isReadVar $k@217 $Perm.Write))
(set-option :timeout 0)
(push) ; 6
(assert (not (or (= $k@217 $Perm.No) true)))
(check-sat)
; unsat
(pop) ; 6
; 0.00s
; (get-info :all-statistics)
(assert (< $k@217 $k@124))
; [eval] x.Set__max >= diz.Set__max
(set-option :timeout 0)
(push) ; 6
(assert (not (>= $t@123 $t@116)))
(check-sat)
; unsat
(pop) ; 6
; 0.00s
; (get-info :all-statistics)
(assert (>= $t@123 $t@116))
(declare-const fvf@218 $FVF<Int>)
(declare-const fvf@219 $FVF<Int>)
(declare-const fvf@220 $FVF<$Seq<$Ref>>)
(declare-const fvf@221 $FVF<$Seq<$Ref>>)
(assert (= ($FVF.lookup_Set__max fvf@218 diz@101) $t@116))
(assert ($Set.equal ($FVF.domain_Set__max fvf@218) ($Set.singleton  diz@101)))
(assert (= ($FVF.lookup_Set__max fvf@219 x@102) $t@123))
(assert ($Set.equal ($FVF.domain_Set__max fvf@219) ($Set.singleton  x@102)))
(assert ($Seq.equal ($FVF.lookup_Set__contents fvf@220 diz@101) $t@118))
(assert ($Set.equal ($FVF.domain_Set__contents fvf@220) ($Set.singleton  diz@101)))
(assert ($Seq.equal ($FVF.lookup_Set__contents fvf@221 x@102) $t@125))
(assert ($Set.equal ($FVF.domain_Set__contents fvf@221) ($Set.singleton  x@102)))
(declare-const k@222 Int)
; [eval] (0 <= k) && (k < x.Set__max)
; [eval] 0 <= k
(push) ; 6
(set-option :timeout 0)
(push) ; 7
(assert (not (not (<= 0 k@222))))
(check-sat)
; unknown
(pop) ; 7
; 0.00s
; (get-info :all-statistics)
(set-option :timeout 0)
(push) ; 7
(assert (not (<= 0 k@222)))
(check-sat)
; unknown
(pop) ; 7
; 0.00s
; (get-info :all-statistics)
(push) ; 7
; [then-branch 42] 0 <= k@222
(assert (<= 0 k@222))
; [eval] k < x.Set__max
(set-option :timeout 0)
(push) ; 8
(assert (not (< $Perm.No (+ (ite (= x@102 diz@101) $k@115 $Perm.No) $k@122))))
(check-sat)
; unsat
(pop) ; 8
; 0.00s
; (get-info :all-statistics)
(declare-const fvf@223 $FVF<Int>)
(assert (implies
  (ite (= x@102 diz@101) (< $Perm.No $k@115) false)
  (= ($FVF.lookup_Set__max fvf@223 x@102) ($FVF.lookup_Set__max fvf@218 x@102))))
(assert (implies
  (< $Perm.No $k@122)
  (= ($FVF.lookup_Set__max fvf@223 x@102) ($FVF.lookup_Set__max fvf@219 x@102))))
(assert ($Set.equal ($FVF.domain_Set__max fvf@223) ($Set.singleton  x@102)))
(pop) ; 7
(push) ; 7
; [else-branch 42] !0 <= k@222
(assert (not (<= 0 k@222)))
(pop) ; 7
(pop) ; 6
(assert ($Set.equal ($FVF.domain_Set__max fvf@223) ($Set.singleton  x@102)))
(assert (implies
  (< $Perm.No $k@122)
  (= ($FVF.lookup_Set__max fvf@223 x@102) ($FVF.lookup_Set__max fvf@219 x@102))))
(assert (implies
  (ite (= x@102 diz@101) (< $Perm.No $k@115) false)
  (= ($FVF.lookup_Set__max fvf@223 x@102) ($FVF.lookup_Set__max fvf@218 x@102))))
(set-option :timeout 0)
(push) ; 6
(assert (not (not (and (<= 0 k@222) (< k@222 ($FVF.lookup_Set__max fvf@223 x@102))))))
(check-sat)
; unknown
(pop) ; 6
; 0.00s
; (get-info :all-statistics)
(assert (and (<= 0 k@222) (< k@222 ($FVF.lookup_Set__max fvf@223 x@102))))
(declare-const $k@224 $Perm)
(assert ($Perm.isValidVar $k@224))
(assert ($Perm.isReadVar $k@224 $Perm.Write))
(set-option :timeout 0)
(push) ; 6
(assert (not (or (= $k@224 $Perm.No) true)))
(check-sat)
; unsat
(pop) ; 6
; 0.00s
; (get-info :all-statistics)
; [eval] x.Set__contents[k]
(set-option :timeout 0)
(push) ; 6
(assert (not (< $Perm.No (+ (ite (= x@102 diz@101) $k@117 $Perm.No) $k@124))))
(check-sat)
; unsat
(pop) ; 6
; 0.00s
; (get-info :all-statistics)
(declare-const fvf@225 $FVF<$Seq<$Ref>>)
(assert (implies
  (ite (= x@102 diz@101) (< $Perm.No $k@117) false)
  ($Seq.equal
    ($FVF.lookup_Set__contents fvf@225 x@102)
    ($FVF.lookup_Set__contents fvf@220 x@102))))
(assert (implies
  (< $Perm.No $k@124)
  ($Seq.equal
    ($FVF.lookup_Set__contents fvf@225 x@102)
    ($FVF.lookup_Set__contents fvf@221 x@102))))
(assert ($Set.equal ($FVF.domain_Set__contents fvf@225) ($Set.singleton  x@102)))
(set-option :timeout 0)
(push) ; 6
(assert (not (forall (($x Int) ($y Int)) (!
  (implies
    (and
      (and (<= 0 $x) (< $x ($FVF.lookup_Set__max fvf@223 x@102)))
      (and (<= 0 $y) (< $y ($FVF.lookup_Set__max fvf@223 x@102)))
      (=
        ($Seq.index ($FVF.lookup_Set__contents fvf@225 x@102) $x)
        ($Seq.index ($FVF.lookup_Set__contents fvf@225 x@102) $y)))
    (= $x $y))
  :pattern (($Seq.index ($FVF.lookup_Set__contents fvf@225 x@102) $x) ($Seq.index
    ($FVF.lookup_Set__contents fvf@225 x@102)
    $y))))))
(check-sat)
; unsat
(pop) ; 6
; 0.00s
; (get-info :all-statistics)
(declare-fun invOf@226 ($Ref) Int)
(assert (forall (($r $Ref)) (!
  (implies
    (and
      (<= 0 (invOf@226 $r))
      (< (invOf@226 $r) ($FVF.lookup_Set__max fvf@223 x@102)))
    (= ($Seq.index ($FVF.lookup_Set__contents fvf@225 x@102) (invOf@226 $r)) $r))
  :pattern ((invOf@226 $r)))))
(assert (forall ((k@222 Int)) (!
  (implies
    (and (<= 0 k@222) (< k@222 ($FVF.lookup_Set__max fvf@223 x@102)))
    (=
      (invOf@226 ($Seq.index ($FVF.lookup_Set__contents fvf@225 x@102) k@222))
      k@222))
  :pattern (($Seq.index ($FVF.lookup_Set__contents fvf@225 x@102) k@222)))))
(declare-const fvf@227 $FVF<Bool>)
; Precomputing split data for Lookup(Set__contents,fvf@225,x@102)[k@222].Ref__Boolean_value # $k@224
(define-fun $permsTaken17 (($r $Ref)) $Perm
  ($Perm.min
    (ite
      (and
        (<= 0 (invOf@226 $r))
        (< (invOf@226 $r) ($FVF.lookup_Set__max fvf@223 x@102)))
      $k@224
      $Perm.No)
    (ite
      (= $r ($Seq.index ($FVF.lookup_Set__contents fvf@225 x@102) k@222))
      (-
        (ite
          (and (<= 0 (invOf@129 $r)) (< (invOf@129 $r) $t@123))
          $k@127
          $Perm.No)
        ($permsTaken15 $r))
      $Perm.No)))
(define-fun $permsTaken18 (($r $Ref)) $Perm
  ($Perm.min
    (-
      (ite
        (and
          (<= 0 (invOf@226 $r))
          (< (invOf@226 $r) ($FVF.lookup_Set__max fvf@223 x@102)))
        $k@224
        $Perm.No)
      ($permsTaken17 $r))
    (ite
      (= $r ($Seq.index ($FVF.lookup_Set__contents fvf@225 x@102) k@222))
      (-
        (ite
          (and (<= 0 (invOf@121 $r)) (< (invOf@121 $r) $t@116))
          $Perm.Write
          $Perm.No)
        ($permsTaken16 $r))
      $Perm.No)))
; Done precomputing, updating quantified heap chunks
; Constrain original permissions $k@224
(assert (forall (($r $Ref)) (!
  (implies
    (not
      (=
        (-
          (ite
            (and (<= 0 (invOf@129 $r)) (< (invOf@129 $r) $t@123))
            $k@127
            $Perm.No)
          ($permsTaken15 $r))
        $Perm.No))
    (<
      (ite
        (and
          (<= 0 (invOf@226 $r))
          (< (invOf@226 $r) ($FVF.lookup_Set__max fvf@223 x@102)))
        $k@224
        $Perm.No)
      (-
        (ite
          (and (<= 0 (invOf@129 $r)) (< (invOf@129 $r) $t@123))
          $k@127
          $Perm.No)
        ($permsTaken15 $r))))
  :pattern ((invOf@129 $r))
  :pattern ((invOf@129 $r))
  :pattern ((invOf@226 $r))
  :pattern ((invOf@226 $r))
  :pattern ((invOf@129 $r))
  :pattern ((invOf@129 $r)))))
; Enough permissions taken?
(set-option :timeout 500)
(push) ; 6
(assert (not (=
  (-
    (ite
      (and
        (<=
          0
          (invOf@226 ($Seq.index ($FVF.lookup_Set__contents fvf@225 x@102) k@222)))
        (<
          (invOf@226 ($Seq.index ($FVF.lookup_Set__contents fvf@225 x@102) k@222))
          ($FVF.lookup_Set__max fvf@223 x@102)))
      $k@224
      $Perm.No)
    ($permsTaken17 ($Seq.index ($FVF.lookup_Set__contents fvf@225 x@102) k@222)))
  $Perm.No)))
(check-sat)
; unknown
(pop) ; 6
; 0.00s
; (get-info :all-statistics)
; Constrain original permissions $k@224
(assert (forall (($r $Ref)) (!
  (implies
    (not
      (=
        (-
          (ite
            (and (<= 0 (invOf@121 $r)) (< (invOf@121 $r) $t@116))
            $Perm.Write
            $Perm.No)
          ($permsTaken16 $r))
        $Perm.No))
    (<
      (ite
        (and
          (<= 0 (invOf@226 $r))
          (< (invOf@226 $r) ($FVF.lookup_Set__max fvf@223 x@102)))
        $k@224
        $Perm.No)
      (-
        (ite
          (and (<= 0 (invOf@121 $r)) (< (invOf@121 $r) $t@116))
          $Perm.Write
          $Perm.No)
        ($permsTaken16 $r))))
  :pattern ((invOf@121 $r))
  :pattern ((invOf@121 $r))
  :pattern ((invOf@226 $r))
  :pattern ((invOf@226 $r))
  :pattern ((invOf@121 $r))
  :pattern ((invOf@121 $r)))))
; Enough permissions taken?
(set-option :timeout 500)
(push) ; 6
(assert (not (=
  (-
    (-
      (ite
        (and
          (<=
            0
            (invOf@226 ($Seq.index
              ($FVF.lookup_Set__contents fvf@225 x@102)
              k@222)))
          (<
            (invOf@226 ($Seq.index
              ($FVF.lookup_Set__contents fvf@225 x@102)
              k@222))
            ($FVF.lookup_Set__max fvf@223 x@102)))
        $k@224
        $Perm.No)
      ($permsTaken17 ($Seq.index ($FVF.lookup_Set__contents fvf@225 x@102) k@222)))
    ($permsTaken18 ($Seq.index ($FVF.lookup_Set__contents fvf@225 x@102) k@222)))
  $Perm.No)))
(check-sat)
; unsat
(pop) ; 6
; 0.01s
; (get-info :all-statistics)
; Final check that enough permissions have been taken
; Done splitting
(assert (forall (($r $Ref)) (!
  (implies
    (and
      (<
        $Perm.No
        (-
          (ite
            (and (<= 0 (invOf@121 $r)) (< (invOf@121 $r) $t@116))
            $Perm.Write
            $Perm.No)
          ($permsTaken16 $r)))
      ($Set.in $r ($FVF.domain_Ref__Boolean_value fvf@227)))
    (=
      ($FVF.lookup_Ref__Boolean_value fvf@227 $r)
      ($FVF.lookup_Ref__Boolean_value $t@120 $r)))
  :pattern (($FVF.lookup_Ref__Boolean_value fvf@227 $r) (invOf@121 $r))
  :pattern (($FVF.lookup_Ref__Boolean_value $t@120 $r) (invOf@121 $r)))))
(assert (forall (($r $Ref)) (!
  (implies
    (and
      (<
        $Perm.No
        (-
          (ite
            (and (<= 0 (invOf@129 $r)) (< (invOf@129 $r) $t@123))
            $k@127
            $Perm.No)
          ($permsTaken15 $r)))
      ($Set.in $r ($FVF.domain_Ref__Boolean_value fvf@227)))
    (=
      ($FVF.lookup_Ref__Boolean_value fvf@227 $r)
      ($FVF.lookup_Ref__Boolean_value $t@128 $r)))
  :pattern (($FVF.lookup_Ref__Boolean_value fvf@227 $r) (invOf@129 $r))
  :pattern (($FVF.lookup_Ref__Boolean_value $t@128 $r) (invOf@129 $r)))))
(assert (forall (($r $Ref)) (!
  (iff
    ($Set.in $r ($FVF.domain_Ref__Boolean_value fvf@227))
    (and
      (<= 0 (invOf@226 $r))
      (< (invOf@226 $r) ($FVF.lookup_Set__max fvf@223 x@102))))
  :pattern (($Set.in $r ($FVF.domain_Ref__Boolean_value fvf@227))))))
; [eval] (0 <= i) && (i <= diz.Set__max)
; [eval] 0 <= i
(push) ; 6
(set-option :timeout 0)
(push) ; 7
(assert (not false))
(check-sat)
; unknown
(pop) ; 7
; 0.00s
; (get-info :all-statistics)
(push) ; 7
; [then-branch 43] True
; [eval] i <= diz.Set__max
(pop) ; 7
; [dead else-branch 43] False
(pop) ; 6
(set-option :timeout 0)
(push) ; 6
(assert (not (<= 0 $t@116)))
(check-sat)
; unsat
(pop) ; 6
; 0.00s
; (get-info :all-statistics)
(assert (<= 0 $t@116))
; [eval] (forall k: Int :: (0 <= k) && (k < i) ==> (diz.Set__contents[k].Ref__Boolean_value == diz.Set__contents[k].Ref__Boolean_value && x.Set__contents[k].Ref__Boolean_value))
(declare-const k@228 Int)
(push) ; 6
; [eval] (0 <= k) && (k < i) ==> (diz.Set__contents[k].Ref__Boolean_value == diz.Set__contents[k].Ref__Boolean_value && x.Set__contents[k].Ref__Boolean_value)
; [eval] (0 <= k) && (k < i)
; [eval] 0 <= k
(push) ; 7
(set-option :timeout 0)
(push) ; 8
(assert (not (not (<= 0 k@228))))
(check-sat)
; unknown
(pop) ; 8
; 0.00s
; (get-info :all-statistics)
(set-option :timeout 0)
(push) ; 8
(assert (not (<= 0 k@228)))
(check-sat)
; unknown
(pop) ; 8
; 0.00s
; (get-info :all-statistics)
(push) ; 8
; [then-branch 44] 0 <= k@228
(assert (<= 0 k@228))
; [eval] k < i
(pop) ; 8
(push) ; 8
; [else-branch 44] !0 <= k@228
(assert (not (<= 0 k@228)))
(pop) ; 8
(pop) ; 7
(push) ; 7
(set-option :timeout 0)
(push) ; 8
(assert (not (not (and (<= 0 k@228) (< k@228 0)))))
(check-sat)
; unsat
(pop) ; 8
; 0.00s
; (get-info :all-statistics)
(set-option :timeout 0)
(push) ; 8
(assert (not (and (<= 0 k@228) (< k@228 0))))
(check-sat)
; unknown
(pop) ; 8
; 0.00s
; (get-info :all-statistics)
; [dead then-branch 45] 0 <= k@228 && k@228 < 0
(push) ; 8
; [else-branch 45] !0 <= k@228 && k@228 < 0
(assert (not (and (<= 0 k@228) (< k@228 0))))
(pop) ; 8
(pop) ; 7
(pop) ; 6
(set-option :timeout 0)
(push) ; 6
(assert (not (forall ((k@228 Int)) (!
  true
  :pattern ()
  :pattern ()
  :pattern ()))))
(check-sat)
; unsat
(pop) ; 6
; 0.00s
; (get-info :all-statistics)
(assert (forall ((k@228 Int)) (!
  true
  :pattern ()
  :pattern ()
  :pattern ())))
; Continue after loop
(declare-const $t@229 $Snap)
(declare-const $t@230 $Snap)
(assert (= $t@229 ($Snap.combine $t@230 $Snap.unit)))
(declare-const $t@231 $Snap)
(assert (= $t@230 ($Snap.combine $t@231 $Snap.unit)))
(declare-const $t@232 $Snap)
(assert (= $t@231 ($Snap.combine $t@232 $Snap.unit)))
(declare-const $t@233 $Snap)
(declare-const $t@234 $FVF<Bool>)
(assert (= $t@232 ($Snap.combine $t@233 ($SortWrappers.$FVF<Bool>To$Snap $t@234))))
(declare-const $t@235 $Snap)
(assert (= $t@233 ($Snap.combine $t@235 $Snap.unit)))
(declare-const $t@236 $Snap)
(declare-const $t@237 $Seq<$Ref>)
(assert (= $t@235 ($Snap.combine $t@236 ($SortWrappers.$Seq<$Ref>To$Snap $t@237))))
(declare-const $t@238 $Snap)
(assert (= $t@236 ($Snap.combine $t@238 $Snap.unit)))
(declare-const $t@239 $Snap)
(declare-const $t@240 Int)
(assert (= $t@238 ($Snap.combine $t@239 ($SortWrappers.IntTo$Snap $t@240))))
(declare-const $t@241 $Snap)
(assert (= $t@239 ($Snap.combine $t@241 $Snap.unit)))
(declare-const $t@242 $Snap)
(declare-const $t@243 $FVF<Bool>)
(assert (= $t@241 ($Snap.combine $t@242 ($SortWrappers.$FVF<Bool>To$Snap $t@243))))
(declare-const $t@244 $Snap)
(assert (= $t@242 ($Snap.combine $t@244 $Snap.unit)))
(declare-const $t@245 Int)
(declare-const $t@246 $Seq<$Ref>)
(assert (=
  $t@244
  ($Snap.combine
    ($SortWrappers.IntTo$Snap $t@245)
    ($SortWrappers.$Seq<$Ref>To$Snap $t@246))))
(declare-const $t@247 Int)
(assert (=
  ($SortWrappers.IntTo$Snap $t@245)
  ($Snap.combine ($SortWrappers.IntTo$Snap $t@247) $Snap.unit)))
(declare-const $k@248 $Perm)
(assert ($Perm.isValidVar $k@248))
(assert ($Perm.isReadVar $k@248 $Perm.Write))
(assert (implies (< $Perm.No (- $k@115 $k@205)) (= $t@247 $t@116)))
; [eval] diz.Set__max > 0
(set-option :timeout 0)
(push) ; 6
(assert (not (not (= (+ (- $k@115 $k@205) $k@248) $Perm.No))))
(check-sat)
; unsat
(pop) ; 6
; 0.00s
; (get-info :all-statistics)
(assert (not (= (+ (- $k@115 $k@205) $k@248) $Perm.No)))
(assert (> $t@247 0))
(declare-const $k@249 $Perm)
(assert ($Perm.isValidVar $k@249))
(assert ($Perm.isReadVar $k@249 $Perm.Write))
(assert (implies (< $Perm.No (- $k@117 $k@206)) ($Seq.equal $t@246 $t@118)))
; [eval] |diz.Set__contents| == diz.Set__max
; [eval] |diz.Set__contents|
(set-option :timeout 0)
(push) ; 6
(assert (not (not (= (+ (- $k@117 $k@206) $k@249) $Perm.No))))
(check-sat)
; unsat
(pop) ; 6
; 0.00s
; (get-info :all-statistics)
(assert (not (= (+ (- $k@117 $k@206) $k@249) $Perm.No)))
(assert (= ($Seq.length $t@246) $t@247))
(declare-const k@250 Int)
(push) ; 6
; [eval] (0 <= k) && (k < diz.Set__max)
; [eval] 0 <= k
(push) ; 7
(set-option :timeout 0)
(push) ; 8
(assert (not (not (<= 0 k@250))))
(check-sat)
; unknown
(pop) ; 8
; 0.00s
; (get-info :all-statistics)
(set-option :timeout 0)
(push) ; 8
(assert (not (<= 0 k@250)))
(check-sat)
; unknown
(pop) ; 8
; 0.00s
; (get-info :all-statistics)
(push) ; 8
; [then-branch 46] 0 <= k@250
(assert (<= 0 k@250))
; [eval] k < diz.Set__max
(pop) ; 8
(push) ; 8
; [else-branch 46] !0 <= k@250
(assert (not (<= 0 k@250)))
(pop) ; 8
(pop) ; 7
(assert (and (<= 0 k@250) (< k@250 $t@247)))
; [eval] diz.Set__contents[k]
(pop) ; 6
(declare-fun invOf@251 ($Ref) Int)
(assert (forall (($r $Ref)) (!
  (implies
    (and (<= 0 (invOf@251 $r)) (< (invOf@251 $r) $t@247))
    (= ($Seq.index $t@246 (invOf@251 $r)) $r))
  :pattern ((invOf@251 $r)))))
(assert (forall ((k@250 Int)) (!
  (implies
    (and (<= 0 k@250) (< k@250 $t@247))
    (= (invOf@251 ($Seq.index $t@246 k@250)) k@250))
  :pattern (($Seq.index $t@246 k@250)))))
(assert (forall ((k@250 Int)) (!
  (iff
    ($Set.in ($Seq.index $t@246 k@250) ($FVF.domain_Ref__Boolean_value $t@243))
    (and (<= 0 k@250) (< k@250 $t@247)))
  :pattern (($Set.in
    ($Seq.index $t@246 k@250)
    ($FVF.domain_Ref__Boolean_value $t@243))))))
(assert (forall ((k@250 Int)) (!
  (implies
    (and (<= 0 k@250) (< k@250 $t@247))
    (not (= ($Seq.index $t@246 k@250) $Ref.null)))
  :pattern (($Seq.index $t@246 k@250)))))
; [eval] x != null
(declare-const $k@252 $Perm)
(assert ($Perm.isValidVar $k@252))
(assert ($Perm.isReadVar $k@252 $Perm.Write))
(assert (implies (< $Perm.No (- $k@122 $k@216)) (= $t@240 $t@123)))
; [eval] x.Set__max > 0
(set-option :timeout 0)
(push) ; 6
(assert (not (not (= (+ (- $k@122 $k@216) $k@252) $Perm.No))))
(check-sat)
; unsat
(pop) ; 6
; 0.00s
; (get-info :all-statistics)
(assert (not (= (+ (- $k@122 $k@216) $k@252) $Perm.No)))
(assert (> $t@240 0))
(declare-const $k@253 $Perm)
(assert ($Perm.isValidVar $k@253))
(assert ($Perm.isReadVar $k@253 $Perm.Write))
(assert (implies (< $Perm.No (- $k@124 $k@217)) ($Seq.equal $t@237 $t@125)))
; [eval] x.Set__max >= diz.Set__max
(assert (>= $t@240 $t@247))
(declare-const k@254 Int)
(push) ; 6
; [eval] (0 <= k) && (k < x.Set__max)
; [eval] 0 <= k
(push) ; 7
(set-option :timeout 0)
(push) ; 8
(assert (not (not (<= 0 k@254))))
(check-sat)
; unknown
(pop) ; 8
; 0.00s
; (get-info :all-statistics)
(set-option :timeout 0)
(push) ; 8
(assert (not (<= 0 k@254)))
(check-sat)
; unknown
(pop) ; 8
; 0.00s
; (get-info :all-statistics)
(push) ; 8
; [then-branch 47] 0 <= k@254
(assert (<= 0 k@254))
; [eval] k < x.Set__max
(pop) ; 8
(push) ; 8
; [else-branch 47] !0 <= k@254
(assert (not (<= 0 k@254)))
(pop) ; 8
(pop) ; 7
(assert (and (<= 0 k@254) (< k@254 $t@240)))
; [eval] x.Set__contents[k]
(set-option :timeout 0)
(push) ; 7
(assert (not (not (= (+ (- $k@124 $k@217) $k@253) $Perm.No))))
(check-sat)
; unsat
(pop) ; 7
; 0.00s
; (get-info :all-statistics)
(assert (not (= (+ (- $k@124 $k@217) $k@253) $Perm.No)))
(declare-const $k@255 $Perm)
(assert ($Perm.isValidVar $k@255))
(assert ($Perm.isReadVar $k@255 $Perm.Write))
(pop) ; 6
(assert (not (= (+ (- $k@124 $k@217) $k@253) $Perm.No)))
(assert ($Perm.isValidVar $k@255))
(assert ($Perm.isReadVar $k@255 $Perm.Write))
(declare-fun invOf@256 ($Ref) Int)
(assert (forall (($r $Ref)) (!
  (implies
    (and (<= 0 (invOf@256 $r)) (< (invOf@256 $r) $t@240))
    (= ($Seq.index $t@237 (invOf@256 $r)) $r))
  :pattern ((invOf@256 $r)))))
(assert (forall ((k@254 Int)) (!
  (implies
    (and (<= 0 k@254) (< k@254 $t@240))
    (= (invOf@256 ($Seq.index $t@237 k@254)) k@254))
  :pattern (($Seq.index $t@237 k@254)))))
(assert (forall ((k@254 Int)) (!
  (iff
    ($Set.in ($Seq.index $t@237 k@254) ($FVF.domain_Ref__Boolean_value $t@234))
    (and (<= 0 k@254) (< k@254 $t@240)))
  :pattern (($Set.in
    ($Seq.index $t@237 k@254)
    ($FVF.domain_Ref__Boolean_value $t@234))))))
(assert (forall ((k@254 Int)) (!
  (implies
    (and (and (<= 0 k@254) (< k@254 $t@240)) (< $Perm.No $k@255))
    (not (= ($Seq.index $t@237 k@254) $Ref.null)))
  :pattern (($Seq.index $t@237 k@254)))))
(assert (< $Perm.No $k@255))
; [eval] (0 <= i) && (i <= diz.Set__max)
; [eval] 0 <= i
(push) ; 6
(set-option :timeout 0)
(push) ; 7
(assert (not (not (<= 0 i@137))))
(check-sat)
; unknown
(pop) ; 7
; 0.00s
; (get-info :all-statistics)
(set-option :timeout 0)
(push) ; 7
(assert (not (<= 0 i@137)))
(check-sat)
; unknown
(pop) ; 7
; 0.00s
; (get-info :all-statistics)
(push) ; 7
; [then-branch 48] 0 <= i@137
(assert (<= 0 i@137))
; [eval] i <= diz.Set__max
(pop) ; 7
(push) ; 7
; [else-branch 48] !0 <= i@137
(assert (not (<= 0 i@137)))
(pop) ; 7
(pop) ; 6
(assert (and (<= 0 i@137) (<= i@137 $t@247)))
; [eval] (forall k: Int :: (0 <= k) && (k < i) ==> (diz.Set__contents[k].Ref__Boolean_value == diz.Set__contents[k].Ref__Boolean_value && x.Set__contents[k].Ref__Boolean_value))
(declare-const k@257 Int)
(push) ; 6
; [eval] (0 <= k) && (k < i) ==> (diz.Set__contents[k].Ref__Boolean_value == diz.Set__contents[k].Ref__Boolean_value && x.Set__contents[k].Ref__Boolean_value)
; [eval] (0 <= k) && (k < i)
; [eval] 0 <= k
(push) ; 7
(set-option :timeout 0)
(push) ; 8
(assert (not (not (<= 0 k@257))))
(check-sat)
; unknown
(pop) ; 8
; 0.00s
; (get-info :all-statistics)
(set-option :timeout 0)
(push) ; 8
(assert (not (<= 0 k@257)))
(check-sat)
; unknown
(pop) ; 8
; 0.00s
; (get-info :all-statistics)
(push) ; 8
; [then-branch 49] 0 <= k@257
(assert (<= 0 k@257))
; [eval] k < i
(pop) ; 8
(push) ; 8
; [else-branch 49] !0 <= k@257
(assert (not (<= 0 k@257)))
(pop) ; 8
(pop) ; 7
(push) ; 7
(set-option :timeout 0)
(push) ; 8
(assert (not (not (and (<= 0 k@257) (< k@257 i@137)))))
(check-sat)
; unknown
(pop) ; 8
; 0.00s
; (get-info :all-statistics)
(set-option :timeout 0)
(push) ; 8
(assert (not (and (<= 0 k@257) (< k@257 i@137))))
(check-sat)
; unknown
(pop) ; 8
; 0.00s
; (get-info :all-statistics)
(push) ; 8
; [then-branch 50] 0 <= k@257 && k@257 < i@137
(assert (and (<= 0 k@257) (< k@257 i@137)))
; [eval] diz.Set__contents[k].Ref__Boolean_value == diz.Set__contents[k].Ref__Boolean_value && x.Set__contents[k].Ref__Boolean_value
; [eval] diz.Set__contents[k]
(set-option :timeout 0)
(push) ; 9
(assert (not (not (= ($Seq.index $t@246 k@257) $Ref.null))))
(check-sat)
; unsat
(pop) ; 9
; 0.00s
; (get-info :all-statistics)
(set-option :timeout 0)
(push) ; 9
(assert (not (<
  $Perm.No
  (+
    (+
      (+
        (-
          (-
            (ite
              (and
                (<= 0 (invOf@121 ($Seq.index $t@246 k@257)))
                (< (invOf@121 ($Seq.index $t@246 k@257)) $t@116))
              $Perm.Write
              $Perm.No)
            ($permsTaken16 ($Seq.index $t@246 k@257)))
          ($permsTaken18 ($Seq.index $t@246 k@257)))
        (-
          (-
            (ite
              (and
                (<= 0 (invOf@129 ($Seq.index $t@246 k@257)))
                (< (invOf@129 ($Seq.index $t@246 k@257)) $t@123))
              $k@127
              $Perm.No)
            ($permsTaken15 ($Seq.index $t@246 k@257)))
          ($permsTaken17 ($Seq.index $t@246 k@257))))
      (ite
        (and
          (<= 0 (invOf@251 ($Seq.index $t@246 k@257)))
          (< (invOf@251 ($Seq.index $t@246 k@257)) $t@247))
        $Perm.Write
        $Perm.No))
    (ite
      (and
        (<= 0 (invOf@256 ($Seq.index $t@246 k@257)))
        (< (invOf@256 ($Seq.index $t@246 k@257)) $t@240))
      $k@255
      $Perm.No)))))
(check-sat)
; unsat
(pop) ; 9
; 0.03s
; (get-info :all-statistics)
(declare-const fvf@258 $FVF<Bool>)
(assert (forall (($r $Ref)) (!
  (implies
    (and
      (<
        $Perm.No
        (-
          (-
            (ite
              (and (<= 0 (invOf@121 $r)) (< (invOf@121 $r) $t@116))
              $Perm.Write
              $Perm.No)
            ($permsTaken16 $r))
          ($permsTaken18 $r)))
      ($Set.in $r ($FVF.domain_Ref__Boolean_value fvf@258)))
    (=
      ($FVF.lookup_Ref__Boolean_value fvf@258 $r)
      ($FVF.lookup_Ref__Boolean_value $t@120 $r)))
  :pattern (($FVF.lookup_Ref__Boolean_value fvf@258 $r) (invOf@121 $r))
  :pattern (($FVF.lookup_Ref__Boolean_value $t@120 $r) (invOf@121 $r)))))
(assert (forall (($r $Ref)) (!
  (implies
    (and
      (<
        $Perm.No
        (-
          (-
            (ite
              (and (<= 0 (invOf@129 $r)) (< (invOf@129 $r) $t@123))
              $k@127
              $Perm.No)
            ($permsTaken15 $r))
          ($permsTaken17 $r)))
      ($Set.in $r ($FVF.domain_Ref__Boolean_value fvf@258)))
    (=
      ($FVF.lookup_Ref__Boolean_value fvf@258 $r)
      ($FVF.lookup_Ref__Boolean_value $t@128 $r)))
  :pattern (($FVF.lookup_Ref__Boolean_value fvf@258 $r) (invOf@129 $r))
  :pattern (($FVF.lookup_Ref__Boolean_value $t@128 $r) (invOf@129 $r)))))
(assert (forall (($r $Ref)) (!
  (implies
    (and
      (and (<= 0 (invOf@251 $r)) (< (invOf@251 $r) $t@247))
      ($Set.in $r ($FVF.domain_Ref__Boolean_value fvf@258)))
    (=
      ($FVF.lookup_Ref__Boolean_value fvf@258 $r)
      ($FVF.lookup_Ref__Boolean_value $t@243 $r)))
  :pattern (($FVF.lookup_Ref__Boolean_value fvf@258 $r) (invOf@251 $r))
  :pattern (($FVF.lookup_Ref__Boolean_value $t@243 $r) (invOf@251 $r)))))
(assert (forall (($r $Ref)) (!
  (implies
    (and
      (ite
        (and (<= 0 (invOf@256 $r)) (< (invOf@256 $r) $t@240))
        (< $Perm.No $k@255)
        false)
      ($Set.in $r ($FVF.domain_Ref__Boolean_value fvf@258)))
    (=
      ($FVF.lookup_Ref__Boolean_value fvf@258 $r)
      ($FVF.lookup_Ref__Boolean_value $t@234 $r)))
  :pattern (($FVF.lookup_Ref__Boolean_value fvf@258 $r) (invOf@256 $r))
  :pattern (($FVF.lookup_Ref__Boolean_value $t@234 $r) (invOf@256 $r)))))
(assert (forall ((k@257 Int)) (!
  (iff
    ($Set.in ($Seq.index $t@246 k@257) ($FVF.domain_Ref__Boolean_value fvf@258))
    (and (and (<= 0 k@257) (< k@257 i@137)) (<= $t@116 $t@123)))
  :pattern (($Set.in
    ($Seq.index $t@246 k@257)
    ($FVF.domain_Ref__Boolean_value fvf@258))))))
; [eval] diz.Set__contents[k].Ref__Boolean_value && x.Set__contents[k].Ref__Boolean_value
; [eval] diz.Set__contents[k]
(set-option :timeout 0)
(push) ; 9
(assert (not (not (= ($Seq.index $t@246 k@257) $Ref.null))))
(check-sat)
; unsat
(pop) ; 9
; 0.00s
; (get-info :all-statistics)
(set-option :timeout 0)
(push) ; 9
(assert (not (<
  $Perm.No
  (+
    (+
      (+
        (-
          (-
            (ite
              (and
                (<= 0 (invOf@121 ($Seq.index $t@246 k@257)))
                (< (invOf@121 ($Seq.index $t@246 k@257)) $t@116))
              $Perm.Write
              $Perm.No)
            ($permsTaken16 ($Seq.index $t@246 k@257)))
          ($permsTaken18 ($Seq.index $t@246 k@257)))
        (-
          (-
            (ite
              (and
                (<= 0 (invOf@129 ($Seq.index $t@246 k@257)))
                (< (invOf@129 ($Seq.index $t@246 k@257)) $t@123))
              $k@127
              $Perm.No)
            ($permsTaken15 ($Seq.index $t@246 k@257)))
          ($permsTaken17 ($Seq.index $t@246 k@257))))
      (ite
        (and
          (<= 0 (invOf@251 ($Seq.index $t@246 k@257)))
          (< (invOf@251 ($Seq.index $t@246 k@257)) $t@247))
        $Perm.Write
        $Perm.No))
    (ite
      (and
        (<= 0 (invOf@256 ($Seq.index $t@246 k@257)))
        (< (invOf@256 ($Seq.index $t@246 k@257)) $t@240))
      $k@255
      $Perm.No)))))
(check-sat)
; unsat
(pop) ; 9
; 0.03s
; (get-info :all-statistics)
(declare-const fvf@259 $FVF<Bool>)
(push) ; 9
(set-option :timeout 0)
(push) ; 10
(assert (not (not ($FVF.lookup_Ref__Boolean_value fvf@258 ($Seq.index $t@246 k@257)))))
(check-sat)
; unknown
(pop) ; 10
; 0.03s
; (get-info :all-statistics)
(set-option :timeout 0)
(push) ; 10
(assert (not ($FVF.lookup_Ref__Boolean_value fvf@258 ($Seq.index $t@246 k@257))))
(check-sat)
; unknown
(pop) ; 10
; 0.03s
; (get-info :all-statistics)
(push) ; 10
; [then-branch 51] Lookup(Ref__Boolean_value,fvf@258,$t@246[k@257])
(assert ($FVF.lookup_Ref__Boolean_value fvf@258 ($Seq.index $t@246 k@257)))
; [eval] x.Set__contents[k]
(set-option :timeout 0)
(push) ; 11
(assert (not (not (= ($Seq.index $t@237 k@257) $Ref.null))))
(check-sat)
; unsat
(pop) ; 11
; 0.00s
; (get-info :all-statistics)
(set-option :timeout 0)
(push) ; 11
(assert (not (<
  $Perm.No
  (+
    (+
      (+
        (-
          (-
            (ite
              (and
                (<= 0 (invOf@121 ($Seq.index $t@237 k@257)))
                (< (invOf@121 ($Seq.index $t@237 k@257)) $t@116))
              $Perm.Write
              $Perm.No)
            ($permsTaken16 ($Seq.index $t@237 k@257)))
          ($permsTaken18 ($Seq.index $t@237 k@257)))
        (-
          (-
            (ite
              (and
                (<= 0 (invOf@129 ($Seq.index $t@237 k@257)))
                (< (invOf@129 ($Seq.index $t@237 k@257)) $t@123))
              $k@127
              $Perm.No)
            ($permsTaken15 ($Seq.index $t@237 k@257)))
          ($permsTaken17 ($Seq.index $t@237 k@257))))
      (ite
        (and
          (<= 0 (invOf@251 ($Seq.index $t@237 k@257)))
          (< (invOf@251 ($Seq.index $t@237 k@257)) $t@247))
        $Perm.Write
        $Perm.No))
    (ite
      (and
        (<= 0 (invOf@256 ($Seq.index $t@237 k@257)))
        (< (invOf@256 ($Seq.index $t@237 k@257)) $t@240))
      $k@255
      $Perm.No)))))
(check-sat)
; unsat
(pop) ; 11
; 0.05s
; (get-info :all-statistics)
(declare-const fvf@260 $FVF<Bool>)
(assert (forall (($r $Ref)) (!
  (implies
    (and
      (<
        $Perm.No
        (-
          (-
            (ite
              (and (<= 0 (invOf@121 $r)) (< (invOf@121 $r) $t@116))
              $Perm.Write
              $Perm.No)
            ($permsTaken16 $r))
          ($permsTaken18 $r)))
      ($Set.in $r ($FVF.domain_Ref__Boolean_value fvf@260)))
    (=
      ($FVF.lookup_Ref__Boolean_value fvf@260 $r)
      ($FVF.lookup_Ref__Boolean_value $t@120 $r)))
  :pattern (($FVF.lookup_Ref__Boolean_value fvf@260 $r) (invOf@121 $r))
  :pattern (($FVF.lookup_Ref__Boolean_value $t@120 $r) (invOf@121 $r)))))
(assert (forall (($r $Ref)) (!
  (implies
    (and
      (<
        $Perm.No
        (-
          (-
            (ite
              (and (<= 0 (invOf@129 $r)) (< (invOf@129 $r) $t@123))
              $k@127
              $Perm.No)
            ($permsTaken15 $r))
          ($permsTaken17 $r)))
      ($Set.in $r ($FVF.domain_Ref__Boolean_value fvf@260)))
    (=
      ($FVF.lookup_Ref__Boolean_value fvf@260 $r)
      ($FVF.lookup_Ref__Boolean_value $t@128 $r)))
  :pattern (($FVF.lookup_Ref__Boolean_value fvf@260 $r) (invOf@129 $r))
  :pattern (($FVF.lookup_Ref__Boolean_value $t@128 $r) (invOf@129 $r)))))
(assert (forall (($r $Ref)) (!
  (implies
    (and
      (and (<= 0 (invOf@251 $r)) (< (invOf@251 $r) $t@247))
      ($Set.in $r ($FVF.domain_Ref__Boolean_value fvf@260)))
    (=
      ($FVF.lookup_Ref__Boolean_value fvf@260 $r)
      ($FVF.lookup_Ref__Boolean_value $t@243 $r)))
  :pattern (($FVF.lookup_Ref__Boolean_value fvf@260 $r) (invOf@251 $r))
  :pattern (($FVF.lookup_Ref__Boolean_value $t@243 $r) (invOf@251 $r)))))
(assert (forall (($r $Ref)) (!
  (implies
    (and
      (ite
        (and (<= 0 (invOf@256 $r)) (< (invOf@256 $r) $t@240))
        (< $Perm.No $k@255)
        false)
      ($Set.in $r ($FVF.domain_Ref__Boolean_value fvf@260)))
    (=
      ($FVF.lookup_Ref__Boolean_value fvf@260 $r)
      ($FVF.lookup_Ref__Boolean_value $t@234 $r)))
  :pattern (($FVF.lookup_Ref__Boolean_value fvf@260 $r) (invOf@256 $r))
  :pattern (($FVF.lookup_Ref__Boolean_value $t@234 $r) (invOf@256 $r)))))
(assert (forall ((k@257 Int)) (!
  (iff
    ($Set.in ($Seq.index $t@237 k@257) ($FVF.domain_Ref__Boolean_value fvf@260))
    (and
      ($FVF.lookup_Ref__Boolean_value fvf@258 ($Seq.index $t@246 k@257))
      (and (<= 0 k@257) (< k@257 i@137))
      (<= $t@116 $t@123)))
  :pattern (($Set.in
    ($Seq.index $t@237 k@257)
    ($FVF.domain_Ref__Boolean_value fvf@260))))))
(pop) ; 10
(push) ; 10
; [else-branch 51] !Lookup(Ref__Boolean_value,fvf@258,$t@246[k@257])
(assert (not ($FVF.lookup_Ref__Boolean_value fvf@258 ($Seq.index $t@246 k@257))))
(pop) ; 10
(pop) ; 9
(assert (forall ((k@257 Int)) (!
  (iff
    ($Set.in ($Seq.index $t@237 k@257) ($FVF.domain_Ref__Boolean_value fvf@260))
    (and
      ($FVF.lookup_Ref__Boolean_value fvf@258 ($Seq.index $t@246 k@257))
      (and (<= 0 k@257) (< k@257 i@137))
      (<= $t@116 $t@123)))
  :pattern (($Set.in
    ($Seq.index $t@237 k@257)
    ($FVF.domain_Ref__Boolean_value fvf@260))))))
(assert (forall (($r $Ref)) (!
  (implies
    (and
      (ite
        (and (<= 0 (invOf@256 $r)) (< (invOf@256 $r) $t@240))
        (< $Perm.No $k@255)
        false)
      ($Set.in $r ($FVF.domain_Ref__Boolean_value fvf@260)))
    (=
      ($FVF.lookup_Ref__Boolean_value fvf@260 $r)
      ($FVF.lookup_Ref__Boolean_value $t@234 $r)))
  :pattern (($FVF.lookup_Ref__Boolean_value fvf@260 $r) (invOf@256 $r))
  :pattern (($FVF.lookup_Ref__Boolean_value $t@234 $r) (invOf@256 $r)))))
(assert (forall (($r $Ref)) (!
  (implies
    (and
      (and (<= 0 (invOf@251 $r)) (< (invOf@251 $r) $t@247))
      ($Set.in $r ($FVF.domain_Ref__Boolean_value fvf@260)))
    (=
      ($FVF.lookup_Ref__Boolean_value fvf@260 $r)
      ($FVF.lookup_Ref__Boolean_value $t@243 $r)))
  :pattern (($FVF.lookup_Ref__Boolean_value fvf@260 $r) (invOf@251 $r))
  :pattern (($FVF.lookup_Ref__Boolean_value $t@243 $r) (invOf@251 $r)))))
(assert (forall (($r $Ref)) (!
  (implies
    (and
      (<
        $Perm.No
        (-
          (-
            (ite
              (and (<= 0 (invOf@129 $r)) (< (invOf@129 $r) $t@123))
              $k@127
              $Perm.No)
            ($permsTaken15 $r))
          ($permsTaken17 $r)))
      ($Set.in $r ($FVF.domain_Ref__Boolean_value fvf@260)))
    (=
      ($FVF.lookup_Ref__Boolean_value fvf@260 $r)
      ($FVF.lookup_Ref__Boolean_value $t@128 $r)))
  :pattern (($FVF.lookup_Ref__Boolean_value fvf@260 $r) (invOf@129 $r))
  :pattern (($FVF.lookup_Ref__Boolean_value $t@128 $r) (invOf@129 $r)))))
(assert (forall (($r $Ref)) (!
  (implies
    (and
      (<
        $Perm.No
        (-
          (-
            (ite
              (and (<= 0 (invOf@121 $r)) (< (invOf@121 $r) $t@116))
              $Perm.Write
              $Perm.No)
            ($permsTaken16 $r))
          ($permsTaken18 $r)))
      ($Set.in $r ($FVF.domain_Ref__Boolean_value fvf@260)))
    (=
      ($FVF.lookup_Ref__Boolean_value fvf@260 $r)
      ($FVF.lookup_Ref__Boolean_value $t@120 $r)))
  :pattern (($FVF.lookup_Ref__Boolean_value fvf@260 $r) (invOf@121 $r))
  :pattern (($FVF.lookup_Ref__Boolean_value $t@120 $r) (invOf@121 $r)))))
(pop) ; 8
(push) ; 8
; [else-branch 50] !0 <= k@257 && k@257 < i@137
(assert (not (and (<= 0 k@257) (< k@257 i@137))))
(pop) ; 8
(pop) ; 7
(assert (forall (($r $Ref)) (!
  (implies
    (and
      (<
        $Perm.No
        (-
          (-
            (ite
              (and (<= 0 (invOf@121 $r)) (< (invOf@121 $r) $t@116))
              $Perm.Write
              $Perm.No)
            ($permsTaken16 $r))
          ($permsTaken18 $r)))
      ($Set.in $r ($FVF.domain_Ref__Boolean_value fvf@260)))
    (=
      ($FVF.lookup_Ref__Boolean_value fvf@260 $r)
      ($FVF.lookup_Ref__Boolean_value $t@120 $r)))
  :pattern (($FVF.lookup_Ref__Boolean_value fvf@260 $r) (invOf@121 $r))
  :pattern (($FVF.lookup_Ref__Boolean_value $t@120 $r) (invOf@121 $r)))))
(assert (forall (($r $Ref)) (!
  (implies
    (and
      (<
        $Perm.No
        (-
          (-
            (ite
              (and (<= 0 (invOf@129 $r)) (< (invOf@129 $r) $t@123))
              $k@127
              $Perm.No)
            ($permsTaken15 $r))
          ($permsTaken17 $r)))
      ($Set.in $r ($FVF.domain_Ref__Boolean_value fvf@260)))
    (=
      ($FVF.lookup_Ref__Boolean_value fvf@260 $r)
      ($FVF.lookup_Ref__Boolean_value $t@128 $r)))
  :pattern (($FVF.lookup_Ref__Boolean_value fvf@260 $r) (invOf@129 $r))
  :pattern (($FVF.lookup_Ref__Boolean_value $t@128 $r) (invOf@129 $r)))))
(assert (forall (($r $Ref)) (!
  (implies
    (and
      (and (<= 0 (invOf@251 $r)) (< (invOf@251 $r) $t@247))
      ($Set.in $r ($FVF.domain_Ref__Boolean_value fvf@260)))
    (=
      ($FVF.lookup_Ref__Boolean_value fvf@260 $r)
      ($FVF.lookup_Ref__Boolean_value $t@243 $r)))
  :pattern (($FVF.lookup_Ref__Boolean_value fvf@260 $r) (invOf@251 $r))
  :pattern (($FVF.lookup_Ref__Boolean_value $t@243 $r) (invOf@251 $r)))))
(assert (forall (($r $Ref)) (!
  (implies
    (and
      (ite
        (and (<= 0 (invOf@256 $r)) (< (invOf@256 $r) $t@240))
        (< $Perm.No $k@255)
        false)
      ($Set.in $r ($FVF.domain_Ref__Boolean_value fvf@260)))
    (=
      ($FVF.lookup_Ref__Boolean_value fvf@260 $r)
      ($FVF.lookup_Ref__Boolean_value $t@234 $r)))
  :pattern (($FVF.lookup_Ref__Boolean_value fvf@260 $r) (invOf@256 $r))
  :pattern (($FVF.lookup_Ref__Boolean_value $t@234 $r) (invOf@256 $r)))))
(assert (forall ((k@257 Int)) (!
  (iff
    ($Set.in ($Seq.index $t@237 k@257) ($FVF.domain_Ref__Boolean_value fvf@260))
    (and
      ($FVF.lookup_Ref__Boolean_value fvf@258 ($Seq.index $t@246 k@257))
      (and (<= 0 k@257) (< k@257 i@137))
      (<= $t@116 $t@123)))
  :pattern (($Set.in
    ($Seq.index $t@237 k@257)
    ($FVF.domain_Ref__Boolean_value fvf@260))))))
(assert (forall ((k@257 Int)) (!
  (iff
    ($Set.in ($Seq.index $t@246 k@257) ($FVF.domain_Ref__Boolean_value fvf@258))
    (and (and (<= 0 k@257) (< k@257 i@137)) (<= $t@116 $t@123)))
  :pattern (($Set.in
    ($Seq.index $t@246 k@257)
    ($FVF.domain_Ref__Boolean_value fvf@258))))))
(assert (forall (($r $Ref)) (!
  (implies
    (and
      (ite
        (and (<= 0 (invOf@256 $r)) (< (invOf@256 $r) $t@240))
        (< $Perm.No $k@255)
        false)
      ($Set.in $r ($FVF.domain_Ref__Boolean_value fvf@258)))
    (=
      ($FVF.lookup_Ref__Boolean_value fvf@258 $r)
      ($FVF.lookup_Ref__Boolean_value $t@234 $r)))
  :pattern (($FVF.lookup_Ref__Boolean_value fvf@258 $r) (invOf@256 $r))
  :pattern (($FVF.lookup_Ref__Boolean_value $t@234 $r) (invOf@256 $r)))))
(assert (forall (($r $Ref)) (!
  (implies
    (and
      (and (<= 0 (invOf@251 $r)) (< (invOf@251 $r) $t@247))
      ($Set.in $r ($FVF.domain_Ref__Boolean_value fvf@258)))
    (=
      ($FVF.lookup_Ref__Boolean_value fvf@258 $r)
      ($FVF.lookup_Ref__Boolean_value $t@243 $r)))
  :pattern (($FVF.lookup_Ref__Boolean_value fvf@258 $r) (invOf@251 $r))
  :pattern (($FVF.lookup_Ref__Boolean_value $t@243 $r) (invOf@251 $r)))))
(assert (forall (($r $Ref)) (!
  (implies
    (and
      (<
        $Perm.No
        (-
          (-
            (ite
              (and (<= 0 (invOf@129 $r)) (< (invOf@129 $r) $t@123))
              $k@127
              $Perm.No)
            ($permsTaken15 $r))
          ($permsTaken17 $r)))
      ($Set.in $r ($FVF.domain_Ref__Boolean_value fvf@258)))
    (=
      ($FVF.lookup_Ref__Boolean_value fvf@258 $r)
      ($FVF.lookup_Ref__Boolean_value $t@128 $r)))
  :pattern (($FVF.lookup_Ref__Boolean_value fvf@258 $r) (invOf@129 $r))
  :pattern (($FVF.lookup_Ref__Boolean_value $t@128 $r) (invOf@129 $r)))))
(assert (forall (($r $Ref)) (!
  (implies
    (and
      (<
        $Perm.No
        (-
          (-
            (ite
              (and (<= 0 (invOf@121 $r)) (< (invOf@121 $r) $t@116))
              $Perm.Write
              $Perm.No)
            ($permsTaken16 $r))
          ($permsTaken18 $r)))
      ($Set.in $r ($FVF.domain_Ref__Boolean_value fvf@258)))
    (=
      ($FVF.lookup_Ref__Boolean_value fvf@258 $r)
      ($FVF.lookup_Ref__Boolean_value $t@120 $r)))
  :pattern (($FVF.lookup_Ref__Boolean_value fvf@258 $r) (invOf@121 $r))
  :pattern (($FVF.lookup_Ref__Boolean_value $t@120 $r) (invOf@121 $r)))))
(pop) ; 6
(assert (forall (($r $Ref)) (!
  (implies
    (and
      (<
        $Perm.No
        (-
          (-
            (ite
              (and (<= 0 (invOf@121 $r)) (< (invOf@121 $r) $t@116))
              $Perm.Write
              $Perm.No)
            ($permsTaken16 $r))
          ($permsTaken18 $r)))
      ($Set.in $r ($FVF.domain_Ref__Boolean_value fvf@260)))
    (=
      ($FVF.lookup_Ref__Boolean_value fvf@260 $r)
      ($FVF.lookup_Ref__Boolean_value $t@120 $r)))
  :pattern (($FVF.lookup_Ref__Boolean_value fvf@260 $r) (invOf@121 $r))
  :pattern (($FVF.lookup_Ref__Boolean_value $t@120 $r) (invOf@121 $r)))))
(assert (forall (($r $Ref)) (!
  (implies
    (and
      (<
        $Perm.No
        (-
          (-
            (ite
              (and (<= 0 (invOf@129 $r)) (< (invOf@129 $r) $t@123))
              $k@127
              $Perm.No)
            ($permsTaken15 $r))
          ($permsTaken17 $r)))
      ($Set.in $r ($FVF.domain_Ref__Boolean_value fvf@260)))
    (=
      ($FVF.lookup_Ref__Boolean_value fvf@260 $r)
      ($FVF.lookup_Ref__Boolean_value $t@128 $r)))
  :pattern (($FVF.lookup_Ref__Boolean_value fvf@260 $r) (invOf@129 $r))
  :pattern (($FVF.lookup_Ref__Boolean_value $t@128 $r) (invOf@129 $r)))))
(assert (forall (($r $Ref)) (!
  (implies
    (and
      (and (<= 0 (invOf@251 $r)) (< (invOf@251 $r) $t@247))
      ($Set.in $r ($FVF.domain_Ref__Boolean_value fvf@260)))
    (=
      ($FVF.lookup_Ref__Boolean_value fvf@260 $r)
      ($FVF.lookup_Ref__Boolean_value $t@243 $r)))
  :pattern (($FVF.lookup_Ref__Boolean_value fvf@260 $r) (invOf@251 $r))
  :pattern (($FVF.lookup_Ref__Boolean_value $t@243 $r) (invOf@251 $r)))))
(assert (forall (($r $Ref)) (!
  (implies
    (and
      (ite
        (and (<= 0 (invOf@256 $r)) (< (invOf@256 $r) $t@240))
        (< $Perm.No $k@255)
        false)
      ($Set.in $r ($FVF.domain_Ref__Boolean_value fvf@260)))
    (=
      ($FVF.lookup_Ref__Boolean_value fvf@260 $r)
      ($FVF.lookup_Ref__Boolean_value $t@234 $r)))
  :pattern (($FVF.lookup_Ref__Boolean_value fvf@260 $r) (invOf@256 $r))
  :pattern (($FVF.lookup_Ref__Boolean_value $t@234 $r) (invOf@256 $r)))))
(assert (forall ((k@257 Int)) (!
  (iff
    ($Set.in ($Seq.index $t@237 k@257) ($FVF.domain_Ref__Boolean_value fvf@260))
    (and
      ($FVF.lookup_Ref__Boolean_value fvf@258 ($Seq.index $t@246 k@257))
      (and (<= 0 k@257) (< k@257 i@137))
      (<= $t@116 $t@123)))
  :pattern (($Set.in
    ($Seq.index $t@237 k@257)
    ($FVF.domain_Ref__Boolean_value fvf@260))))))
(assert (forall ((k@257 Int)) (!
  (iff
    ($Set.in ($Seq.index $t@246 k@257) ($FVF.domain_Ref__Boolean_value fvf@258))
    (and (and (<= 0 k@257) (< k@257 i@137)) (<= $t@116 $t@123)))
  :pattern (($Set.in
    ($Seq.index $t@246 k@257)
    ($FVF.domain_Ref__Boolean_value fvf@258))))))
(assert (forall (($r $Ref)) (!
  (implies
    (and
      (ite
        (and (<= 0 (invOf@256 $r)) (< (invOf@256 $r) $t@240))
        (< $Perm.No $k@255)
        false)
      ($Set.in $r ($FVF.domain_Ref__Boolean_value fvf@258)))
    (=
      ($FVF.lookup_Ref__Boolean_value fvf@258 $r)
      ($FVF.lookup_Ref__Boolean_value $t@234 $r)))
  :pattern (($FVF.lookup_Ref__Boolean_value fvf@258 $r) (invOf@256 $r))
  :pattern (($FVF.lookup_Ref__Boolean_value $t@234 $r) (invOf@256 $r)))))
(assert (forall (($r $Ref)) (!
  (implies
    (and
      (and (<= 0 (invOf@251 $r)) (< (invOf@251 $r) $t@247))
      ($Set.in $r ($FVF.domain_Ref__Boolean_value fvf@258)))
    (=
      ($FVF.lookup_Ref__Boolean_value fvf@258 $r)
      ($FVF.lookup_Ref__Boolean_value $t@243 $r)))
  :pattern (($FVF.lookup_Ref__Boolean_value fvf@258 $r) (invOf@251 $r))
  :pattern (($FVF.lookup_Ref__Boolean_value $t@243 $r) (invOf@251 $r)))))
(assert (forall (($r $Ref)) (!
  (implies
    (and
      (<
        $Perm.No
        (-
          (-
            (ite
              (and (<= 0 (invOf@129 $r)) (< (invOf@129 $r) $t@123))
              $k@127
              $Perm.No)
            ($permsTaken15 $r))
          ($permsTaken17 $r)))
      ($Set.in $r ($FVF.domain_Ref__Boolean_value fvf@258)))
    (=
      ($FVF.lookup_Ref__Boolean_value fvf@258 $r)
      ($FVF.lookup_Ref__Boolean_value $t@128 $r)))
  :pattern (($FVF.lookup_Ref__Boolean_value fvf@258 $r) (invOf@129 $r))
  :pattern (($FVF.lookup_Ref__Boolean_value $t@128 $r) (invOf@129 $r)))))
(assert (forall (($r $Ref)) (!
  (implies
    (and
      (<
        $Perm.No
        (-
          (-
            (ite
              (and (<= 0 (invOf@121 $r)) (< (invOf@121 $r) $t@116))
              $Perm.Write
              $Perm.No)
            ($permsTaken16 $r))
          ($permsTaken18 $r)))
      ($Set.in $r ($FVF.domain_Ref__Boolean_value fvf@258)))
    (=
      ($FVF.lookup_Ref__Boolean_value fvf@258 $r)
      ($FVF.lookup_Ref__Boolean_value $t@120 $r)))
  :pattern (($FVF.lookup_Ref__Boolean_value fvf@258 $r) (invOf@121 $r))
  :pattern (($FVF.lookup_Ref__Boolean_value $t@120 $r) (invOf@121 $r)))))
(assert (forall ((k@257 Int)) (!
  (implies
    (and (<= 0 k@257) (< k@257 i@137))
    (=
      ($FVF.lookup_Ref__Boolean_value fvf@258 ($Seq.index $t@246 k@257))
      (and
        ($FVF.lookup_Ref__Boolean_value fvf@258 ($Seq.index $t@246 k@257))
        ($FVF.lookup_Ref__Boolean_value fvf@260 ($Seq.index $t@237 k@257)))))
  :pattern (($Seq.index $t@246 k@257))
  :pattern (($Seq.index $t@246 k@257))
  :pattern (($Seq.index $t@237 k@257)))))
; [eval] !(i < diz.Set__max)
; [eval] i < diz.Set__max
(assert (not (< i@137 $t@247)))
(set-option :timeout 0)
(check-sat)
; unknown
(declare-const $k@261 $Perm)
(assert ($Perm.isValidVar $k@261))
(assert ($Perm.isReadVar $k@261 $Perm.Write))
(set-option :timeout 0)
(push) ; 6
(assert (not (or (= $k@261 $Perm.No) true)))
(check-sat)
; unsat
(pop) ; 6
; 0.00s
; (get-info :all-statistics)
(assert (< $k@261 (+ (- $k@115 $k@205) $k@248)))
; [eval] diz.Set__max > 0
(declare-const $k@262 $Perm)
(assert ($Perm.isValidVar $k@262))
(assert ($Perm.isReadVar $k@262 $Perm.Write))
(set-option :timeout 0)
(push) ; 6
(assert (not (or (= $k@262 $Perm.No) true)))
(check-sat)
; unsat
(pop) ; 6
; 0.00s
; (get-info :all-statistics)
(assert (< $k@262 (+ (- $k@117 $k@206) $k@249)))
; [eval] |diz.Set__contents| == diz.Set__max
; [eval] |diz.Set__contents|
(declare-const fvf@263 $FVF<Int>)
(declare-const fvf@264 $FVF<Int>)
(declare-const fvf@265 $FVF<$Seq<$Ref>>)
(declare-const fvf@266 $FVF<$Seq<$Ref>>)
(assert (= ($FVF.lookup_Set__max fvf@263 diz@101) $t@247))
(assert ($Set.equal ($FVF.domain_Set__max fvf@263) ($Set.singleton  diz@101)))
(assert (= ($FVF.lookup_Set__max fvf@264 x@102) $t@240))
(assert ($Set.equal ($FVF.domain_Set__max fvf@264) ($Set.singleton  x@102)))
(assert ($Seq.equal ($FVF.lookup_Set__contents fvf@265 diz@101) $t@246))
(assert ($Set.equal ($FVF.domain_Set__contents fvf@265) ($Set.singleton  diz@101)))
(assert ($Seq.equal ($FVF.lookup_Set__contents fvf@266 x@102) $t@237))
(assert ($Set.equal ($FVF.domain_Set__contents fvf@266) ($Set.singleton  x@102)))
(declare-const k@267 Int)
; [eval] (0 <= k) && (k < diz.Set__max)
; [eval] 0 <= k
(push) ; 6
(set-option :timeout 0)
(push) ; 7
(assert (not (not (<= 0 k@267))))
(check-sat)
; unknown
(pop) ; 7
; 0.00s
; (get-info :all-statistics)
(set-option :timeout 0)
(push) ; 7
(assert (not (<= 0 k@267)))
(check-sat)
; unknown
(pop) ; 7
; 0.00s
; (get-info :all-statistics)
(push) ; 7
; [then-branch 52] 0 <= k@267
(assert (<= 0 k@267))
; [eval] k < diz.Set__max
(set-option :timeout 0)
(push) ; 8
(assert (not (<
  $Perm.No
  (+
    (+ (- $k@115 $k@205) $k@248)
    (ite (= diz@101 x@102) (+ (- $k@122 $k@216) $k@252) $Perm.No)))))
(check-sat)
; unsat
(pop) ; 8
; 0.00s
; (get-info :all-statistics)
(declare-const fvf@268 $FVF<Int>)
(assert (implies
  (< $Perm.No (+ (- $k@115 $k@205) $k@248))
  (=
    ($FVF.lookup_Set__max fvf@268 diz@101)
    ($FVF.lookup_Set__max fvf@263 diz@101))))
(assert (implies
  (ite (= diz@101 x@102) (< $Perm.No (+ (- $k@122 $k@216) $k@252)) false)
  (=
    ($FVF.lookup_Set__max fvf@268 diz@101)
    ($FVF.lookup_Set__max fvf@264 diz@101))))
(assert ($Set.equal ($FVF.domain_Set__max fvf@268) ($Set.singleton  diz@101)))
(pop) ; 7
(push) ; 7
; [else-branch 52] !0 <= k@267
(assert (not (<= 0 k@267)))
(pop) ; 7
(pop) ; 6
(assert ($Set.equal ($FVF.domain_Set__max fvf@268) ($Set.singleton  diz@101)))
(assert (implies
  (ite (= diz@101 x@102) (< $Perm.No (+ (- $k@122 $k@216) $k@252)) false)
  (=
    ($FVF.lookup_Set__max fvf@268 diz@101)
    ($FVF.lookup_Set__max fvf@264 diz@101))))
(assert (implies
  (< $Perm.No (+ (- $k@115 $k@205) $k@248))
  (=
    ($FVF.lookup_Set__max fvf@268 diz@101)
    ($FVF.lookup_Set__max fvf@263 diz@101))))
(set-option :timeout 0)
(push) ; 6
(assert (not (not (and (<= 0 k@267) (< k@267 ($FVF.lookup_Set__max fvf@268 diz@101))))))
(check-sat)
; unknown
(pop) ; 6
; 0.00s
; (get-info :all-statistics)
(assert (and (<= 0 k@267) (< k@267 ($FVF.lookup_Set__max fvf@268 diz@101))))
; [eval] diz.Set__contents[k]
(set-option :timeout 0)
(push) ; 6
(assert (not (<
  $Perm.No
  (+
    (+ (- $k@117 $k@206) $k@249)
    (ite (= diz@101 x@102) (+ (- $k@124 $k@217) $k@253) $Perm.No)))))
(check-sat)
; unsat
(pop) ; 6
; 0.00s
; (get-info :all-statistics)
(declare-const fvf@269 $FVF<$Seq<$Ref>>)
(assert (implies
  (< $Perm.No (+ (- $k@117 $k@206) $k@249))
  ($Seq.equal
    ($FVF.lookup_Set__contents fvf@269 diz@101)
    ($FVF.lookup_Set__contents fvf@265 diz@101))))
(assert (implies
  (ite (= diz@101 x@102) (< $Perm.No (+ (- $k@124 $k@217) $k@253)) false)
  ($Seq.equal
    ($FVF.lookup_Set__contents fvf@269 diz@101)
    ($FVF.lookup_Set__contents fvf@266 diz@101))))
(assert ($Set.equal ($FVF.domain_Set__contents fvf@269) ($Set.singleton  diz@101)))
(set-option :timeout 0)
(push) ; 6
(assert (not (forall (($x Int) ($y Int)) (!
  (implies
    (and
      (and (<= 0 $x) (< $x ($FVF.lookup_Set__max fvf@268 diz@101)))
      (and (<= 0 $y) (< $y ($FVF.lookup_Set__max fvf@268 diz@101)))
      (=
        ($Seq.index ($FVF.lookup_Set__contents fvf@269 diz@101) $x)
        ($Seq.index ($FVF.lookup_Set__contents fvf@269 diz@101) $y)))
    (= $x $y))
  :pattern (($Seq.index ($FVF.lookup_Set__contents fvf@269 diz@101) $x) ($Seq.index
    ($FVF.lookup_Set__contents fvf@269 diz@101)
    $y))))))
(check-sat)
; unsat
(pop) ; 6
; 0.00s
; (get-info :all-statistics)
(declare-fun invOf@270 ($Ref) Int)
(assert (forall (($r $Ref)) (!
  (implies
    (and
      (<= 0 (invOf@270 $r))
      (< (invOf@270 $r) ($FVF.lookup_Set__max fvf@268 diz@101)))
    (=
      ($Seq.index ($FVF.lookup_Set__contents fvf@269 diz@101) (invOf@270 $r))
      $r))
  :pattern ((invOf@270 $r)))))
(assert (forall ((k@267 Int)) (!
  (implies
    (and (<= 0 k@267) (< k@267 ($FVF.lookup_Set__max fvf@268 diz@101)))
    (=
      (invOf@270 ($Seq.index ($FVF.lookup_Set__contents fvf@269 diz@101) k@267))
      k@267))
  :pattern (($Seq.index ($FVF.lookup_Set__contents fvf@269 diz@101) k@267)))))
(declare-const fvf@271 $FVF<Bool>)
; Precomputing split data for Lookup(Set__contents,fvf@269,diz@101)[k@267].Ref__Boolean_value # W
(define-fun $permsTaken19 (($r $Ref)) $Perm
  ($Perm.min
    (ite
      (and
        (<= 0 (invOf@270 $r))
        (< (invOf@270 $r) ($FVF.lookup_Set__max fvf@268 diz@101)))
      $Perm.Write
      $Perm.No)
    (ite
      (= $r ($Seq.index ($FVF.lookup_Set__contents fvf@269 diz@101) k@267))
      (ite (and (<= 0 (invOf@256 $r)) (< (invOf@256 $r) $t@240)) $k@255 $Perm.No)
      $Perm.No)))
(define-fun $permsTaken20 (($r $Ref)) $Perm
  ($Perm.min
    (-
      (ite
        (and
          (<= 0 (invOf@270 $r))
          (< (invOf@270 $r) ($FVF.lookup_Set__max fvf@268 diz@101)))
        $Perm.Write
        $Perm.No)
      ($permsTaken19 $r))
    (ite
      (= $r ($Seq.index ($FVF.lookup_Set__contents fvf@269 diz@101) k@267))
      (ite
        (and (<= 0 (invOf@251 $r)) (< (invOf@251 $r) $t@247))
        $Perm.Write
        $Perm.No)
      $Perm.No)))
(define-fun $permsTaken21 (($r $Ref)) $Perm
  ($Perm.min
    (-
      (-
        (ite
          (and
            (<= 0 (invOf@270 $r))
            (< (invOf@270 $r) ($FVF.lookup_Set__max fvf@268 diz@101)))
          $Perm.Write
          $Perm.No)
        ($permsTaken19 $r))
      ($permsTaken20 $r))
    (ite
      (= $r ($Seq.index ($FVF.lookup_Set__contents fvf@269 diz@101) k@267))
      (-
        (-
          (ite
            (and (<= 0 (invOf@129 $r)) (< (invOf@129 $r) $t@123))
            $k@127
            $Perm.No)
          ($permsTaken15 $r))
        ($permsTaken17 $r))
      $Perm.No)))
(define-fun $permsTaken22 (($r $Ref)) $Perm
  ($Perm.min
    (-
      (-
        (-
          (ite
            (and
              (<= 0 (invOf@270 $r))
              (< (invOf@270 $r) ($FVF.lookup_Set__max fvf@268 diz@101)))
            $Perm.Write
            $Perm.No)
          ($permsTaken19 $r))
        ($permsTaken20 $r))
      ($permsTaken21 $r))
    (ite
      (= $r ($Seq.index ($FVF.lookup_Set__contents fvf@269 diz@101) k@267))
      (-
        (-
          (ite
            (and (<= 0 (invOf@121 $r)) (< (invOf@121 $r) $t@116))
            $Perm.Write
            $Perm.No)
          ($permsTaken16 $r))
        ($permsTaken18 $r))
      $Perm.No)))
; Done precomputing, updating quantified heap chunks
; Chunk depleted?
(set-option :timeout 500)
(push) ; 6
(assert (not (forall (($r $Ref)) (!
  (=
    (-
      (ite (and (<= 0 (invOf@256 $r)) (< (invOf@256 $r) $t@240)) $k@255 $Perm.No)
      ($permsTaken19 $r))
    $Perm.No)
  ))))
(check-sat)
; unknown
(pop) ; 6
; 0.12s
; (get-info :all-statistics)
; Enough permissions taken?
(set-option :timeout 500)
(push) ; 6
(assert (not (=
  (-
    (ite
      (and
        (<=
          0
          (invOf@270 ($Seq.index
            ($FVF.lookup_Set__contents fvf@269 diz@101)
            k@267)))
        (<
          (invOf@270 ($Seq.index
            ($FVF.lookup_Set__contents fvf@269 diz@101)
            k@267))
          ($FVF.lookup_Set__max fvf@268 diz@101)))
      $Perm.Write
      $Perm.No)
    ($permsTaken19 ($Seq.index ($FVF.lookup_Set__contents fvf@269 diz@101) k@267)))
  $Perm.No)))
(check-sat)
; unknown
(pop) ; 6
; 0.07s
; (get-info :all-statistics)
; Chunk depleted?
(set-option :timeout 500)
(push) ; 6
(assert (not (forall (($r $Ref)) (!
  (=
    (-
      (ite
        (and (<= 0 (invOf@251 $r)) (< (invOf@251 $r) $t@247))
        $Perm.Write
        $Perm.No)
      ($permsTaken20 $r))
    $Perm.No)
  ))))
(check-sat)
; unknown
(pop) ; 6
; 0.11s
; (get-info :all-statistics)
; Enough permissions taken?
(set-option :timeout 500)
(push) ; 6
(assert (not (=
  (-
    (-
      (ite
        (and
          (<=
            0
            (invOf@270 ($Seq.index
              ($FVF.lookup_Set__contents fvf@269 diz@101)
              k@267)))
          (<
            (invOf@270 ($Seq.index
              ($FVF.lookup_Set__contents fvf@269 diz@101)
              k@267))
            ($FVF.lookup_Set__max fvf@268 diz@101)))
        $Perm.Write
        $Perm.No)
      ($permsTaken19 ($Seq.index
        ($FVF.lookup_Set__contents fvf@269 diz@101)
        k@267)))
    ($permsTaken20 ($Seq.index ($FVF.lookup_Set__contents fvf@269 diz@101) k@267)))
  $Perm.No)))
(check-sat)
; unsat
(pop) ; 6
; 0.01s
; (get-info :all-statistics)
; Final check that enough permissions have been taken
; Done splitting
(assert (forall (($r $Ref)) (!
  (implies
    (and
      (<
        $Perm.No
        (-
          (-
            (ite
              (and (<= 0 (invOf@121 $r)) (< (invOf@121 $r) $t@116))
              $Perm.Write
              $Perm.No)
            ($permsTaken16 $r))
          ($permsTaken18 $r)))
      ($Set.in $r ($FVF.domain_Ref__Boolean_value fvf@271)))
    (=
      ($FVF.lookup_Ref__Boolean_value fvf@271 $r)
      ($FVF.lookup_Ref__Boolean_value $t@120 $r)))
  :pattern (($FVF.lookup_Ref__Boolean_value fvf@271 $r) (invOf@121 $r))
  :pattern (($FVF.lookup_Ref__Boolean_value $t@120 $r) (invOf@121 $r)))))
(assert (forall (($r $Ref)) (!
  (implies
    (and
      (<
        $Perm.No
        (-
          (-
            (ite
              (and (<= 0 (invOf@129 $r)) (< (invOf@129 $r) $t@123))
              $k@127
              $Perm.No)
            ($permsTaken15 $r))
          ($permsTaken17 $r)))
      ($Set.in $r ($FVF.domain_Ref__Boolean_value fvf@271)))
    (=
      ($FVF.lookup_Ref__Boolean_value fvf@271 $r)
      ($FVF.lookup_Ref__Boolean_value $t@128 $r)))
  :pattern (($FVF.lookup_Ref__Boolean_value fvf@271 $r) (invOf@129 $r))
  :pattern (($FVF.lookup_Ref__Boolean_value $t@128 $r) (invOf@129 $r)))))
(assert (forall (($r $Ref)) (!
  (implies
    (and
      (and (<= 0 (invOf@251 $r)) (< (invOf@251 $r) $t@247))
      ($Set.in $r ($FVF.domain_Ref__Boolean_value fvf@271)))
    (=
      ($FVF.lookup_Ref__Boolean_value fvf@271 $r)
      ($FVF.lookup_Ref__Boolean_value $t@243 $r)))
  :pattern (($FVF.lookup_Ref__Boolean_value fvf@271 $r) (invOf@251 $r))
  :pattern (($FVF.lookup_Ref__Boolean_value $t@243 $r) (invOf@251 $r)))))
(assert (forall (($r $Ref)) (!
  (implies
    (and
      (ite
        (and (<= 0 (invOf@256 $r)) (< (invOf@256 $r) $t@240))
        (< $Perm.No $k@255)
        false)
      ($Set.in $r ($FVF.domain_Ref__Boolean_value fvf@271)))
    (=
      ($FVF.lookup_Ref__Boolean_value fvf@271 $r)
      ($FVF.lookup_Ref__Boolean_value $t@234 $r)))
  :pattern (($FVF.lookup_Ref__Boolean_value fvf@271 $r) (invOf@256 $r))
  :pattern (($FVF.lookup_Ref__Boolean_value $t@234 $r) (invOf@256 $r)))))
(assert (forall (($r $Ref)) (!
  (iff
    ($Set.in $r ($FVF.domain_Ref__Boolean_value fvf@271))
    (and
      (<= 0 (invOf@270 $r))
      (< (invOf@270 $r) ($FVF.lookup_Set__max fvf@268 diz@101))))
  :pattern (($Set.in $r ($FVF.domain_Ref__Boolean_value fvf@271))))))
(pop) ; 5
(pop) ; 4
(push) ; 4
; [else-branch 27] !$t@116 <= $t@123
(assert (not (<= $t@116 $t@123)))
(pop) ; 4
; [eval] !(diz.Set__max <= x.Set__max)
; [eval] diz.Set__max <= x.Set__max
(set-option :timeout 0)
(push) ; 4
(assert (not (<= $t@116 $t@123)))
(check-sat)
; unknown
(pop) ; 4
; 0.00s
; (get-info :all-statistics)
(set-option :timeout 0)
(push) ; 4
(assert (not (not (<= $t@116 $t@123))))
(check-sat)
; unknown
(pop) ; 4
; 0.00s
; (get-info :all-statistics)
(push) ; 4
; [then-branch 53] !$t@116 <= $t@123
(assert (not (<= $t@116 $t@123)))
; loop at <no position>
(declare-const j@272 Int)
(declare-const __flatten_13@273 Bool)
(declare-const __flatten_15@274 $Ref)
(declare-const __flatten_14@275 $Ref)
(declare-const __flatten_12@276 $Ref)
(push) ; 5
; Verify loop body
(declare-const $t@277 $Snap)
(declare-const $t@278 $Snap)
(assert (= $t@277 ($Snap.combine $t@278 $Snap.unit)))
(declare-const $t@279 $Snap)
(assert (= $t@278 ($Snap.combine $t@279 $Snap.unit)))
(declare-const $t@280 $Snap)
(declare-const $t@281 $FVF<Bool>)
(assert (= $t@279 ($Snap.combine $t@280 ($SortWrappers.$FVF<Bool>To$Snap $t@281))))
(declare-const $t@282 $Snap)
(assert (= $t@280 ($Snap.combine $t@282 $Snap.unit)))
(declare-const $t@283 $Snap)
(assert (= $t@282 ($Snap.combine $t@283 $Snap.unit)))
(declare-const $t@284 $Snap)
(declare-const $t@285 $Seq<$Ref>)
(assert (= $t@283 ($Snap.combine $t@284 ($SortWrappers.$Seq<$Ref>To$Snap $t@285))))
(declare-const $t@286 $Snap)
(assert (= $t@284 ($Snap.combine $t@286 $Snap.unit)))
(declare-const $t@287 $Snap)
(declare-const $t@288 Int)
(assert (= $t@286 ($Snap.combine $t@287 ($SortWrappers.IntTo$Snap $t@288))))
(declare-const $t@289 $Snap)
(assert (= $t@287 ($Snap.combine $t@289 $Snap.unit)))
(declare-const $t@290 $Snap)
(declare-const $t@291 $FVF<Bool>)
(assert (= $t@289 ($Snap.combine $t@290 ($SortWrappers.$FVF<Bool>To$Snap $t@291))))
(declare-const $t@292 $Snap)
(assert (= $t@290 ($Snap.combine $t@292 $Snap.unit)))
(declare-const $t@293 Int)
(declare-const $t@294 $Seq<$Ref>)
(assert (=
  $t@292
  ($Snap.combine
    ($SortWrappers.IntTo$Snap $t@293)
    ($SortWrappers.$Seq<$Ref>To$Snap $t@294))))
(declare-const $t@295 Int)
(assert (=
  ($SortWrappers.IntTo$Snap $t@293)
  ($Snap.combine ($SortWrappers.IntTo$Snap $t@295) $Snap.unit)))
(declare-const $k@296 $Perm)
(assert ($Perm.isValidVar $k@296))
(assert ($Perm.isReadVar $k@296 $Perm.Write))
; [eval] diz.Set__max > 0
(set-option :timeout 0)
(push) ; 6
(assert (not (not (= $k@296 $Perm.No))))
(check-sat)
; unsat
(pop) ; 6
; 0.00s
; (get-info :all-statistics)
(assert (not (= $k@296 $Perm.No)))
(assert (> $t@295 0))
(declare-const $k@297 $Perm)
(assert ($Perm.isValidVar $k@297))
(assert ($Perm.isReadVar $k@297 $Perm.Write))
; [eval] |diz.Set__contents| == diz.Set__max
; [eval] |diz.Set__contents|
(set-option :timeout 0)
(push) ; 6
(assert (not (not (= $k@297 $Perm.No))))
(check-sat)
; unsat
(pop) ; 6
; 0.00s
; (get-info :all-statistics)
(assert (not (= $k@297 $Perm.No)))
(assert (= ($Seq.length $t@294) $t@295))
(declare-const k@298 Int)
(push) ; 6
; [eval] (0 <= k) && (k < diz.Set__max)
; [eval] 0 <= k
(push) ; 7
(set-option :timeout 0)
(push) ; 8
(assert (not (not (<= 0 k@298))))
(check-sat)
; unknown
(pop) ; 8
; 0.00s
; (get-info :all-statistics)
(set-option :timeout 0)
(push) ; 8
(assert (not (<= 0 k@298)))
(check-sat)
; unknown
(pop) ; 8
; 0.00s
; (get-info :all-statistics)
(push) ; 8
; [then-branch 54] 0 <= k@298
(assert (<= 0 k@298))
; [eval] k < diz.Set__max
(pop) ; 8
(push) ; 8
; [else-branch 54] !0 <= k@298
(assert (not (<= 0 k@298)))
(pop) ; 8
(pop) ; 7
(assert (and (<= 0 k@298) (< k@298 $t@295)))
; [eval] diz.Set__contents[k]
(pop) ; 6
(declare-fun invOf@299 ($Ref) Int)
(assert (forall (($r $Ref)) (!
  (implies
    (and (<= 0 (invOf@299 $r)) (< (invOf@299 $r) $t@295))
    (= ($Seq.index $t@294 (invOf@299 $r)) $r))
  :pattern ((invOf@299 $r)))))
(assert (forall ((k@298 Int)) (!
  (implies
    (and (<= 0 k@298) (< k@298 $t@295))
    (= (invOf@299 ($Seq.index $t@294 k@298)) k@298))
  :pattern (($Seq.index $t@294 k@298)))))
(assert (forall ((k@298 Int)) (!
  (iff
    ($Set.in ($Seq.index $t@294 k@298) ($FVF.domain_Ref__Boolean_value $t@291))
    (and (<= 0 k@298) (< k@298 $t@295)))
  :pattern (($Set.in
    ($Seq.index $t@294 k@298)
    ($FVF.domain_Ref__Boolean_value $t@291))))))
(assert (forall ((k@298 Int)) (!
  (implies
    (and (<= 0 k@298) (< k@298 $t@295))
    (not (= ($Seq.index $t@294 k@298) $Ref.null)))
  :pattern (($Seq.index $t@294 k@298)))))
; [eval] x != null
(declare-const $k@300 $Perm)
(assert ($Perm.isValidVar $k@300))
(assert ($Perm.isReadVar $k@300 $Perm.Write))
(set-option :timeout 0)
(push) ; 6
(assert (not (= diz@101 x@102)))
(check-sat)
; unknown
(pop) ; 6
; 0.00s
; (get-info :all-statistics)
; [eval] x.Set__max > 0
(set-option :timeout 0)
(push) ; 6
(assert (not (not (= $k@300 $Perm.No))))
(check-sat)
; unsat
(pop) ; 6
; 0.00s
; (get-info :all-statistics)
(assert (not (= $k@300 $Perm.No)))
(assert (> $t@288 0))
(declare-const $k@301 $Perm)
(assert ($Perm.isValidVar $k@301))
(assert ($Perm.isReadVar $k@301 $Perm.Write))
(set-option :timeout 0)
(push) ; 6
(assert (not (= diz@101 x@102)))
(check-sat)
; unknown
(pop) ; 6
; 0.00s
; (get-info :all-statistics)
; [eval] diz.Set__max > x.Set__max
(assert (> $t@295 $t@288))
; [eval] (j >= 0) && (j <= x.Set__max)
; [eval] j >= 0
(push) ; 6
(set-option :timeout 0)
(push) ; 7
(assert (not (not (>= j@272 0))))
(check-sat)
; unknown
(pop) ; 7
; 0.00s
; (get-info :all-statistics)
(set-option :timeout 0)
(push) ; 7
(assert (not (>= j@272 0)))
(check-sat)
; unknown
(pop) ; 7
; 0.00s
; (get-info :all-statistics)
(push) ; 7
; [then-branch 55] j@272 >= 0
(assert (>= j@272 0))
; [eval] j <= x.Set__max
(pop) ; 7
(push) ; 7
; [else-branch 55] !j@272 >= 0
(assert (not (>= j@272 0)))
(pop) ; 7
(pop) ; 6
(assert (and (>= j@272 0) (<= j@272 $t@288)))
(declare-const k@302 Int)
(push) ; 6
; [eval] (0 <= k) && (k < x.Set__max)
; [eval] 0 <= k
(push) ; 7
(set-option :timeout 0)
(push) ; 8
(assert (not (not (<= 0 k@302))))
(check-sat)
; unknown
(pop) ; 8
; 0.00s
; (get-info :all-statistics)
(set-option :timeout 0)
(push) ; 8
(assert (not (<= 0 k@302)))
(check-sat)
; unknown
(pop) ; 8
; 0.00s
; (get-info :all-statistics)
(push) ; 8
; [then-branch 56] 0 <= k@302
(assert (<= 0 k@302))
; [eval] k < x.Set__max
(pop) ; 8
(push) ; 8
; [else-branch 56] !0 <= k@302
(assert (not (<= 0 k@302)))
(pop) ; 8
(pop) ; 7
(assert (and (<= 0 k@302) (< k@302 $t@288)))
; [eval] x.Set__contents[k]
(set-option :timeout 0)
(push) ; 7
(assert (not (not (= $k@301 $Perm.No))))
(check-sat)
; unsat
(pop) ; 7
; 0.00s
; (get-info :all-statistics)
(assert (not (= $k@301 $Perm.No)))
(declare-const $k@303 $Perm)
(assert ($Perm.isValidVar $k@303))
(assert ($Perm.isReadVar $k@303 $Perm.Write))
(pop) ; 6
(assert (not (= $k@301 $Perm.No)))
(assert ($Perm.isValidVar $k@303))
(assert ($Perm.isReadVar $k@303 $Perm.Write))
(declare-fun invOf@304 ($Ref) Int)
(assert (forall (($r $Ref)) (!
  (implies
    (and (<= 0 (invOf@304 $r)) (< (invOf@304 $r) $t@288))
    (= ($Seq.index $t@285 (invOf@304 $r)) $r))
  :pattern ((invOf@304 $r)))))
(assert (forall ((k@302 Int)) (!
  (implies
    (and (<= 0 k@302) (< k@302 $t@288))
    (= (invOf@304 ($Seq.index $t@285 k@302)) k@302))
  :pattern (($Seq.index $t@285 k@302)))))
(assert (forall ((k@302 Int)) (!
  (iff
    ($Set.in ($Seq.index $t@285 k@302) ($FVF.domain_Ref__Boolean_value $t@281))
    (and (<= 0 k@302) (< k@302 $t@288)))
  :pattern (($Set.in
    ($Seq.index $t@285 k@302)
    ($FVF.domain_Ref__Boolean_value $t@281))))))
(assert (forall ((k@302 Int)) (!
  (implies
    (and (and (<= 0 k@302) (< k@302 $t@288)) (< $Perm.No $k@303))
    (not (= ($Seq.index $t@285 k@302) $Ref.null)))
  :pattern (($Seq.index $t@285 k@302)))))
(assert (< $Perm.No $k@303))
; [eval] (forall k: Int :: (0 <= k) && (k < j) ==> (diz.Set__contents[k].Ref__Boolean_value == diz.Set__contents[k].Ref__Boolean_value && x.Set__contents[k].Ref__Boolean_value))
(declare-const k@305 Int)
(push) ; 6
; [eval] (0 <= k) && (k < j) ==> (diz.Set__contents[k].Ref__Boolean_value == diz.Set__contents[k].Ref__Boolean_value && x.Set__contents[k].Ref__Boolean_value)
; [eval] (0 <= k) && (k < j)
; [eval] 0 <= k
(push) ; 7
(set-option :timeout 0)
(push) ; 8
(assert (not (not (<= 0 k@305))))
(check-sat)
; unknown
(pop) ; 8
; 0.00s
; (get-info :all-statistics)
(set-option :timeout 0)
(push) ; 8
(assert (not (<= 0 k@305)))
(check-sat)
; unknown
(pop) ; 8
; 0.00s
; (get-info :all-statistics)
(push) ; 8
; [then-branch 57] 0 <= k@305
(assert (<= 0 k@305))
; [eval] k < j
(pop) ; 8
(push) ; 8
; [else-branch 57] !0 <= k@305
(assert (not (<= 0 k@305)))
(pop) ; 8
(pop) ; 7
(push) ; 7
(set-option :timeout 0)
(push) ; 8
(assert (not (not (and (<= 0 k@305) (< k@305 j@272)))))
(check-sat)
; unknown
(pop) ; 8
; 0.00s
; (get-info :all-statistics)
(set-option :timeout 0)
(push) ; 8
(assert (not (and (<= 0 k@305) (< k@305 j@272))))
(check-sat)
; unknown
(pop) ; 8
; 0.00s
; (get-info :all-statistics)
(push) ; 8
; [then-branch 58] 0 <= k@305 && k@305 < j@272
(assert (and (<= 0 k@305) (< k@305 j@272)))
; [eval] diz.Set__contents[k].Ref__Boolean_value == diz.Set__contents[k].Ref__Boolean_value && x.Set__contents[k].Ref__Boolean_value
; [eval] diz.Set__contents[k]
(set-option :timeout 0)
(push) ; 9
(assert (not (not (= ($Seq.index $t@294 k@305) $Ref.null))))
(check-sat)
; unsat
(pop) ; 9
; 0.00s
; (get-info :all-statistics)
(set-option :timeout 0)
(push) ; 9
(assert (not (<
  $Perm.No
  (+
    (ite
      (and
        (<= 0 (invOf@299 ($Seq.index $t@294 k@305)))
        (< (invOf@299 ($Seq.index $t@294 k@305)) $t@295))
      $Perm.Write
      $Perm.No)
    (ite
      (and
        (<= 0 (invOf@304 ($Seq.index $t@294 k@305)))
        (< (invOf@304 ($Seq.index $t@294 k@305)) $t@288))
      $k@303
      $Perm.No)))))
(check-sat)
; unsat
(pop) ; 9
; 0.00s
; (get-info :all-statistics)
(declare-const fvf@306 $FVF<Bool>)
(assert (forall (($r $Ref)) (!
  (implies
    (and
      (and (<= 0 (invOf@299 $r)) (< (invOf@299 $r) $t@295))
      ($Set.in $r ($FVF.domain_Ref__Boolean_value fvf@306)))
    (=
      ($FVF.lookup_Ref__Boolean_value fvf@306 $r)
      ($FVF.lookup_Ref__Boolean_value $t@291 $r)))
  :pattern (($FVF.lookup_Ref__Boolean_value fvf@306 $r) (invOf@299 $r))
  :pattern (($FVF.lookup_Ref__Boolean_value $t@291 $r) (invOf@299 $r)))))
(assert (forall (($r $Ref)) (!
  (implies
    (and
      (ite
        (and (<= 0 (invOf@304 $r)) (< (invOf@304 $r) $t@288))
        (< $Perm.No $k@303)
        false)
      ($Set.in $r ($FVF.domain_Ref__Boolean_value fvf@306)))
    (=
      ($FVF.lookup_Ref__Boolean_value fvf@306 $r)
      ($FVF.lookup_Ref__Boolean_value $t@281 $r)))
  :pattern (($FVF.lookup_Ref__Boolean_value fvf@306 $r) (invOf@304 $r))
  :pattern (($FVF.lookup_Ref__Boolean_value $t@281 $r) (invOf@304 $r)))))
(assert (forall ((k@305 Int)) (!
  (iff
    ($Set.in ($Seq.index $t@294 k@305) ($FVF.domain_Ref__Boolean_value fvf@306))
    (and (and (<= 0 k@305) (< k@305 j@272)) (not (<= $t@116 $t@123))))
  :pattern (($Set.in
    ($Seq.index $t@294 k@305)
    ($FVF.domain_Ref__Boolean_value fvf@306))))))
; [eval] diz.Set__contents[k].Ref__Boolean_value && x.Set__contents[k].Ref__Boolean_value
; [eval] diz.Set__contents[k]
(set-option :timeout 0)
(push) ; 9
(assert (not (not (= ($Seq.index $t@294 k@305) $Ref.null))))
(check-sat)
; unsat
(pop) ; 9
; 0.00s
; (get-info :all-statistics)
(set-option :timeout 0)
(push) ; 9
(assert (not (<
  $Perm.No
  (+
    (ite
      (and
        (<= 0 (invOf@299 ($Seq.index $t@294 k@305)))
        (< (invOf@299 ($Seq.index $t@294 k@305)) $t@295))
      $Perm.Write
      $Perm.No)
    (ite
      (and
        (<= 0 (invOf@304 ($Seq.index $t@294 k@305)))
        (< (invOf@304 ($Seq.index $t@294 k@305)) $t@288))
      $k@303
      $Perm.No)))))
(check-sat)
; unsat
(pop) ; 9
; 0.02s
; (get-info :all-statistics)
(declare-const fvf@307 $FVF<Bool>)
(push) ; 9
(set-option :timeout 0)
(push) ; 10
(assert (not (not ($FVF.lookup_Ref__Boolean_value fvf@306 ($Seq.index $t@294 k@305)))))
(check-sat)
; unknown
(pop) ; 10
; 0.00s
; (get-info :all-statistics)
(set-option :timeout 0)
(push) ; 10
(assert (not ($FVF.lookup_Ref__Boolean_value fvf@306 ($Seq.index $t@294 k@305))))
(check-sat)
; unknown
(pop) ; 10
; 0.00s
; (get-info :all-statistics)
(push) ; 10
; [then-branch 59] Lookup(Ref__Boolean_value,fvf@306,$t@294[k@305])
(assert ($FVF.lookup_Ref__Boolean_value fvf@306 ($Seq.index $t@294 k@305)))
; [eval] x.Set__contents[k]
(set-option :timeout 0)
(push) ; 11
(assert (not (not (= ($Seq.index $t@285 k@305) $Ref.null))))
(check-sat)
; unsat
(pop) ; 11
; 0.00s
; (get-info :all-statistics)
(set-option :timeout 0)
(push) ; 11
(assert (not (<
  $Perm.No
  (+
    (ite
      (and
        (<= 0 (invOf@299 ($Seq.index $t@285 k@305)))
        (< (invOf@299 ($Seq.index $t@285 k@305)) $t@295))
      $Perm.Write
      $Perm.No)
    (ite
      (and
        (<= 0 (invOf@304 ($Seq.index $t@285 k@305)))
        (< (invOf@304 ($Seq.index $t@285 k@305)) $t@288))
      $k@303
      $Perm.No)))))
(check-sat)
; unsat
(pop) ; 11
; 0.00s
; (get-info :all-statistics)
(declare-const fvf@308 $FVF<Bool>)
(assert (forall (($r $Ref)) (!
  (implies
    (and
      (and (<= 0 (invOf@299 $r)) (< (invOf@299 $r) $t@295))
      ($Set.in $r ($FVF.domain_Ref__Boolean_value fvf@308)))
    (=
      ($FVF.lookup_Ref__Boolean_value fvf@308 $r)
      ($FVF.lookup_Ref__Boolean_value $t@291 $r)))
  :pattern (($FVF.lookup_Ref__Boolean_value fvf@308 $r) (invOf@299 $r))
  :pattern (($FVF.lookup_Ref__Boolean_value $t@291 $r) (invOf@299 $r)))))
(assert (forall (($r $Ref)) (!
  (implies
    (and
      (ite
        (and (<= 0 (invOf@304 $r)) (< (invOf@304 $r) $t@288))
        (< $Perm.No $k@303)
        false)
      ($Set.in $r ($FVF.domain_Ref__Boolean_value fvf@308)))
    (=
      ($FVF.lookup_Ref__Boolean_value fvf@308 $r)
      ($FVF.lookup_Ref__Boolean_value $t@281 $r)))
  :pattern (($FVF.lookup_Ref__Boolean_value fvf@308 $r) (invOf@304 $r))
  :pattern (($FVF.lookup_Ref__Boolean_value $t@281 $r) (invOf@304 $r)))))
(assert (forall ((k@305 Int)) (!
  (iff
    ($Set.in ($Seq.index $t@285 k@305) ($FVF.domain_Ref__Boolean_value fvf@308))
    (and
      ($FVF.lookup_Ref__Boolean_value fvf@306 ($Seq.index $t@294 k@305))
      (and (<= 0 k@305) (< k@305 j@272))
      (not (<= $t@116 $t@123))))
  :pattern (($Set.in
    ($Seq.index $t@285 k@305)
    ($FVF.domain_Ref__Boolean_value fvf@308))))))
(pop) ; 10
(push) ; 10
; [else-branch 59] !Lookup(Ref__Boolean_value,fvf@306,$t@294[k@305])
(assert (not ($FVF.lookup_Ref__Boolean_value fvf@306 ($Seq.index $t@294 k@305))))
(pop) ; 10
(pop) ; 9
(assert (forall ((k@305 Int)) (!
  (iff
    ($Set.in ($Seq.index $t@285 k@305) ($FVF.domain_Ref__Boolean_value fvf@308))
    (and
      ($FVF.lookup_Ref__Boolean_value fvf@306 ($Seq.index $t@294 k@305))
      (and (<= 0 k@305) (< k@305 j@272))
      (not (<= $t@116 $t@123))))
  :pattern (($Set.in
    ($Seq.index $t@285 k@305)
    ($FVF.domain_Ref__Boolean_value fvf@308))))))
(assert (forall (($r $Ref)) (!
  (implies
    (and
      (ite
        (and (<= 0 (invOf@304 $r)) (< (invOf@304 $r) $t@288))
        (< $Perm.No $k@303)
        false)
      ($Set.in $r ($FVF.domain_Ref__Boolean_value fvf@308)))
    (=
      ($FVF.lookup_Ref__Boolean_value fvf@308 $r)
      ($FVF.lookup_Ref__Boolean_value $t@281 $r)))
  :pattern (($FVF.lookup_Ref__Boolean_value fvf@308 $r) (invOf@304 $r))
  :pattern (($FVF.lookup_Ref__Boolean_value $t@281 $r) (invOf@304 $r)))))
(assert (forall (($r $Ref)) (!
  (implies
    (and
      (and (<= 0 (invOf@299 $r)) (< (invOf@299 $r) $t@295))
      ($Set.in $r ($FVF.domain_Ref__Boolean_value fvf@308)))
    (=
      ($FVF.lookup_Ref__Boolean_value fvf@308 $r)
      ($FVF.lookup_Ref__Boolean_value $t@291 $r)))
  :pattern (($FVF.lookup_Ref__Boolean_value fvf@308 $r) (invOf@299 $r))
  :pattern (($FVF.lookup_Ref__Boolean_value $t@291 $r) (invOf@299 $r)))))
(pop) ; 8
(push) ; 8
; [else-branch 58] !0 <= k@305 && k@305 < j@272
(assert (not (and (<= 0 k@305) (< k@305 j@272))))
(pop) ; 8
(pop) ; 7
(assert (forall (($r $Ref)) (!
  (implies
    (and
      (and (<= 0 (invOf@299 $r)) (< (invOf@299 $r) $t@295))
      ($Set.in $r ($FVF.domain_Ref__Boolean_value fvf@308)))
    (=
      ($FVF.lookup_Ref__Boolean_value fvf@308 $r)
      ($FVF.lookup_Ref__Boolean_value $t@291 $r)))
  :pattern (($FVF.lookup_Ref__Boolean_value fvf@308 $r) (invOf@299 $r))
  :pattern (($FVF.lookup_Ref__Boolean_value $t@291 $r) (invOf@299 $r)))))
(assert (forall (($r $Ref)) (!
  (implies
    (and
      (ite
        (and (<= 0 (invOf@304 $r)) (< (invOf@304 $r) $t@288))
        (< $Perm.No $k@303)
        false)
      ($Set.in $r ($FVF.domain_Ref__Boolean_value fvf@308)))
    (=
      ($FVF.lookup_Ref__Boolean_value fvf@308 $r)
      ($FVF.lookup_Ref__Boolean_value $t@281 $r)))
  :pattern (($FVF.lookup_Ref__Boolean_value fvf@308 $r) (invOf@304 $r))
  :pattern (($FVF.lookup_Ref__Boolean_value $t@281 $r) (invOf@304 $r)))))
(assert (forall ((k@305 Int)) (!
  (iff
    ($Set.in ($Seq.index $t@285 k@305) ($FVF.domain_Ref__Boolean_value fvf@308))
    (and
      ($FVF.lookup_Ref__Boolean_value fvf@306 ($Seq.index $t@294 k@305))
      (and (<= 0 k@305) (< k@305 j@272))
      (not (<= $t@116 $t@123))))
  :pattern (($Set.in
    ($Seq.index $t@285 k@305)
    ($FVF.domain_Ref__Boolean_value fvf@308))))))
(assert (forall ((k@305 Int)) (!
  (iff
    ($Set.in ($Seq.index $t@294 k@305) ($FVF.domain_Ref__Boolean_value fvf@306))
    (and (and (<= 0 k@305) (< k@305 j@272)) (not (<= $t@116 $t@123))))
  :pattern (($Set.in
    ($Seq.index $t@294 k@305)
    ($FVF.domain_Ref__Boolean_value fvf@306))))))
(assert (forall (($r $Ref)) (!
  (implies
    (and
      (ite
        (and (<= 0 (invOf@304 $r)) (< (invOf@304 $r) $t@288))
        (< $Perm.No $k@303)
        false)
      ($Set.in $r ($FVF.domain_Ref__Boolean_value fvf@306)))
    (=
      ($FVF.lookup_Ref__Boolean_value fvf@306 $r)
      ($FVF.lookup_Ref__Boolean_value $t@281 $r)))
  :pattern (($FVF.lookup_Ref__Boolean_value fvf@306 $r) (invOf@304 $r))
  :pattern (($FVF.lookup_Ref__Boolean_value $t@281 $r) (invOf@304 $r)))))
(assert (forall (($r $Ref)) (!
  (implies
    (and
      (and (<= 0 (invOf@299 $r)) (< (invOf@299 $r) $t@295))
      ($Set.in $r ($FVF.domain_Ref__Boolean_value fvf@306)))
    (=
      ($FVF.lookup_Ref__Boolean_value fvf@306 $r)
      ($FVF.lookup_Ref__Boolean_value $t@291 $r)))
  :pattern (($FVF.lookup_Ref__Boolean_value fvf@306 $r) (invOf@299 $r))
  :pattern (($FVF.lookup_Ref__Boolean_value $t@291 $r) (invOf@299 $r)))))
(pop) ; 6
(assert (forall (($r $Ref)) (!
  (implies
    (and
      (and (<= 0 (invOf@299 $r)) (< (invOf@299 $r) $t@295))
      ($Set.in $r ($FVF.domain_Ref__Boolean_value fvf@308)))
    (=
      ($FVF.lookup_Ref__Boolean_value fvf@308 $r)
      ($FVF.lookup_Ref__Boolean_value $t@291 $r)))
  :pattern (($FVF.lookup_Ref__Boolean_value fvf@308 $r) (invOf@299 $r))
  :pattern (($FVF.lookup_Ref__Boolean_value $t@291 $r) (invOf@299 $r)))))
(assert (forall (($r $Ref)) (!
  (implies
    (and
      (ite
        (and (<= 0 (invOf@304 $r)) (< (invOf@304 $r) $t@288))
        (< $Perm.No $k@303)
        false)
      ($Set.in $r ($FVF.domain_Ref__Boolean_value fvf@308)))
    (=
      ($FVF.lookup_Ref__Boolean_value fvf@308 $r)
      ($FVF.lookup_Ref__Boolean_value $t@281 $r)))
  :pattern (($FVF.lookup_Ref__Boolean_value fvf@308 $r) (invOf@304 $r))
  :pattern (($FVF.lookup_Ref__Boolean_value $t@281 $r) (invOf@304 $r)))))
(assert (forall ((k@305 Int)) (!
  (iff
    ($Set.in ($Seq.index $t@285 k@305) ($FVF.domain_Ref__Boolean_value fvf@308))
    (and
      ($FVF.lookup_Ref__Boolean_value fvf@306 ($Seq.index $t@294 k@305))
      (and (<= 0 k@305) (< k@305 j@272))
      (not (<= $t@116 $t@123))))
  :pattern (($Set.in
    ($Seq.index $t@285 k@305)
    ($FVF.domain_Ref__Boolean_value fvf@308))))))
(assert (forall ((k@305 Int)) (!
  (iff
    ($Set.in ($Seq.index $t@294 k@305) ($FVF.domain_Ref__Boolean_value fvf@306))
    (and (and (<= 0 k@305) (< k@305 j@272)) (not (<= $t@116 $t@123))))
  :pattern (($Set.in
    ($Seq.index $t@294 k@305)
    ($FVF.domain_Ref__Boolean_value fvf@306))))))
(assert (forall (($r $Ref)) (!
  (implies
    (and
      (ite
        (and (<= 0 (invOf@304 $r)) (< (invOf@304 $r) $t@288))
        (< $Perm.No $k@303)
        false)
      ($Set.in $r ($FVF.domain_Ref__Boolean_value fvf@306)))
    (=
      ($FVF.lookup_Ref__Boolean_value fvf@306 $r)
      ($FVF.lookup_Ref__Boolean_value $t@281 $r)))
  :pattern (($FVF.lookup_Ref__Boolean_value fvf@306 $r) (invOf@304 $r))
  :pattern (($FVF.lookup_Ref__Boolean_value $t@281 $r) (invOf@304 $r)))))
(assert (forall (($r $Ref)) (!
  (implies
    (and
      (and (<= 0 (invOf@299 $r)) (< (invOf@299 $r) $t@295))
      ($Set.in $r ($FVF.domain_Ref__Boolean_value fvf@306)))
    (=
      ($FVF.lookup_Ref__Boolean_value fvf@306 $r)
      ($FVF.lookup_Ref__Boolean_value $t@291 $r)))
  :pattern (($FVF.lookup_Ref__Boolean_value fvf@306 $r) (invOf@299 $r))
  :pattern (($FVF.lookup_Ref__Boolean_value $t@291 $r) (invOf@299 $r)))))
(assert (forall ((k@305 Int)) (!
  (implies
    (and (<= 0 k@305) (< k@305 j@272))
    (=
      ($FVF.lookup_Ref__Boolean_value fvf@306 ($Seq.index $t@294 k@305))
      (and
        ($FVF.lookup_Ref__Boolean_value fvf@306 ($Seq.index $t@294 k@305))
        ($FVF.lookup_Ref__Boolean_value fvf@308 ($Seq.index $t@285 k@305)))))
  :pattern (($Seq.index $t@294 k@305))
  :pattern (($Seq.index $t@294 k@305))
  :pattern (($Seq.index $t@285 k@305)))))
; [eval] j < x.Set__max
(assert (< j@272 $t@288))
(set-option :timeout 0)
(check-sat)
; unknown
; [exec]
; __flatten_12 := diz.Set__contents[j]
; [eval] diz.Set__contents[j]
; [exec]
; __flatten_14 := diz.Set__contents[j]
; [eval] diz.Set__contents[j]
; [exec]
; __flatten_15 := x.Set__contents[j]
; [eval] x.Set__contents[j]
; [exec]
; __flatten_13 := __flatten_14.Ref__Boolean_value && __flatten_15.Ref__Boolean_value
; [eval] __flatten_14.Ref__Boolean_value && __flatten_15.Ref__Boolean_value
(set-option :timeout 0)
(push) ; 6
(assert (not (not (= ($Seq.index $t@294 j@272) $Ref.null))))
(check-sat)
; unsat
(pop) ; 6
; 0.00s
; (get-info :all-statistics)
(set-option :timeout 0)
(push) ; 6
(assert (not (<
  $Perm.No
  (+
    (ite
      (and
        (<= 0 (invOf@299 ($Seq.index $t@294 j@272)))
        (< (invOf@299 ($Seq.index $t@294 j@272)) $t@295))
      $Perm.Write
      $Perm.No)
    (ite
      (and
        (<= 0 (invOf@304 ($Seq.index $t@294 j@272)))
        (< (invOf@304 ($Seq.index $t@294 j@272)) $t@288))
      $k@303
      $Perm.No)))))
(check-sat)
; unsat
(pop) ; 6
; 0.00s
; (get-info :all-statistics)
(declare-const fvf@309 $FVF<Bool>)
(assert (implies
  (and
    (<= 0 (invOf@299 ($Seq.index $t@294 j@272)))
    (< (invOf@299 ($Seq.index $t@294 j@272)) $t@295))
  (=
    ($FVF.lookup_Ref__Boolean_value fvf@309 ($Seq.index $t@294 j@272))
    ($FVF.lookup_Ref__Boolean_value $t@291 ($Seq.index $t@294 j@272)))))
(assert (implies
  (ite
    (and
      (<= 0 (invOf@304 ($Seq.index $t@294 j@272)))
      (< (invOf@304 ($Seq.index $t@294 j@272)) $t@288))
    (< $Perm.No $k@303)
    false)
  (=
    ($FVF.lookup_Ref__Boolean_value fvf@309 ($Seq.index $t@294 j@272))
    ($FVF.lookup_Ref__Boolean_value $t@281 ($Seq.index $t@294 j@272)))))
(assert ($Set.equal
  ($FVF.domain_Ref__Boolean_value fvf@309)
  ($Set.singleton  ($Seq.index $t@294 j@272))))
(push) ; 6
(set-option :timeout 0)
(push) ; 7
(assert (not (not ($FVF.lookup_Ref__Boolean_value fvf@309 ($Seq.index $t@294 j@272)))))
(check-sat)
; unknown
(pop) ; 7
; 0.00s
; (get-info :all-statistics)
(set-option :timeout 0)
(push) ; 7
(assert (not ($FVF.lookup_Ref__Boolean_value fvf@309 ($Seq.index $t@294 j@272))))
(check-sat)
; unknown
(pop) ; 7
; 0.00s
; (get-info :all-statistics)
(push) ; 7
; [then-branch 60] Lookup(Ref__Boolean_value,fvf@309,$t@294[j@272])
(assert ($FVF.lookup_Ref__Boolean_value fvf@309 ($Seq.index $t@294 j@272)))
(set-option :timeout 0)
(push) ; 8
(assert (not (not (= ($Seq.index $t@285 j@272) $Ref.null))))
(check-sat)
; unsat
(pop) ; 8
; 0.00s
; (get-info :all-statistics)
(set-option :timeout 0)
(push) ; 8
(assert (not (<
  $Perm.No
  (+
    (ite
      (and
        (<= 0 (invOf@299 ($Seq.index $t@285 j@272)))
        (< (invOf@299 ($Seq.index $t@285 j@272)) $t@295))
      $Perm.Write
      $Perm.No)
    (ite
      (and
        (<= 0 (invOf@304 ($Seq.index $t@285 j@272)))
        (< (invOf@304 ($Seq.index $t@285 j@272)) $t@288))
      $k@303
      $Perm.No)))))
(check-sat)
; unsat
(pop) ; 8
; 0.00s
; (get-info :all-statistics)
(declare-const fvf@310 $FVF<Bool>)
(assert (implies
  (and
    (<= 0 (invOf@299 ($Seq.index $t@285 j@272)))
    (< (invOf@299 ($Seq.index $t@285 j@272)) $t@295))
  (=
    ($FVF.lookup_Ref__Boolean_value fvf@310 ($Seq.index $t@285 j@272))
    ($FVF.lookup_Ref__Boolean_value $t@291 ($Seq.index $t@285 j@272)))))
(assert (implies
  (ite
    (and
      (<= 0 (invOf@304 ($Seq.index $t@285 j@272)))
      (< (invOf@304 ($Seq.index $t@285 j@272)) $t@288))
    (< $Perm.No $k@303)
    false)
  (=
    ($FVF.lookup_Ref__Boolean_value fvf@310 ($Seq.index $t@285 j@272))
    ($FVF.lookup_Ref__Boolean_value $t@281 ($Seq.index $t@285 j@272)))))
(assert ($Set.equal
  ($FVF.domain_Ref__Boolean_value fvf@310)
  ($Set.singleton  ($Seq.index $t@285 j@272))))
(pop) ; 7
(push) ; 7
; [else-branch 60] !Lookup(Ref__Boolean_value,fvf@309,$t@294[j@272])
(assert (not ($FVF.lookup_Ref__Boolean_value fvf@309 ($Seq.index $t@294 j@272))))
(pop) ; 7
(pop) ; 6
(assert ($Set.equal
  ($FVF.domain_Ref__Boolean_value fvf@310)
  ($Set.singleton  ($Seq.index $t@285 j@272))))
(assert (implies
  (ite
    (and
      (<= 0 (invOf@304 ($Seq.index $t@285 j@272)))
      (< (invOf@304 ($Seq.index $t@285 j@272)) $t@288))
    (< $Perm.No $k@303)
    false)
  (=
    ($FVF.lookup_Ref__Boolean_value fvf@310 ($Seq.index $t@285 j@272))
    ($FVF.lookup_Ref__Boolean_value $t@281 ($Seq.index $t@285 j@272)))))
(assert (implies
  (and
    (<= 0 (invOf@299 ($Seq.index $t@285 j@272)))
    (< (invOf@299 ($Seq.index $t@285 j@272)) $t@295))
  (=
    ($FVF.lookup_Ref__Boolean_value fvf@310 ($Seq.index $t@285 j@272))
    ($FVF.lookup_Ref__Boolean_value $t@291 ($Seq.index $t@285 j@272)))))
; [exec]
; __flatten_12.Ref__Boolean_value := __flatten_13
(set-option :timeout 0)
(push) ; 6
(assert (not (not (= ($Seq.index $t@294 j@272) $Ref.null))))
(check-sat)
; unsat
(pop) ; 6
; 0.00s
; (get-info :all-statistics)
(declare-const fvf@311 $FVF<Bool>)
; Precomputing split data for $t@294[j@272].Ref__Boolean_value # W
(define-fun $permsTaken23 (($r $Ref)) $Perm
  ($Perm.min
    (ite (= $r ($Seq.index $t@294 j@272)) $Perm.Write $Perm.No)
    (ite
      (= $r ($Seq.index $t@294 j@272))
      (ite
        (and (<= 0 (invOf@299 $r)) (< (invOf@299 $r) $t@295))
        $Perm.Write
        $Perm.No)
      $Perm.No)))
(define-fun $permsTaken24 (($r $Ref)) $Perm
  ($Perm.min
    (-
      (ite (= $r ($Seq.index $t@294 j@272)) $Perm.Write $Perm.No)
      ($permsTaken23 $r))
    (ite
      (= $r ($Seq.index $t@294 j@272))
      (ite (and (<= 0 (invOf@304 $r)) (< (invOf@304 $r) $t@288)) $k@303 $Perm.No)
      $Perm.No)))
; Done precomputing, updating quantified heap chunks
; Chunk depleted?
(set-option :timeout 500)
(push) ; 6
(assert (not (forall (($r $Ref)) (!
  (=
    (-
      (ite
        (and (<= 0 (invOf@299 $r)) (< (invOf@299 $r) $t@295))
        $Perm.Write
        $Perm.No)
      ($permsTaken23 $r))
    $Perm.No)
  ))))
(check-sat)
; unknown
(pop) ; 6
; 0.01s
; (get-info :all-statistics)
; Enough permissions taken?
(set-option :timeout 500)
(push) ; 6
(assert (not (= (- $Perm.Write ($permsTaken23 ($Seq.index $t@294 j@272))) $Perm.No)))
(check-sat)
; unsat
(pop) ; 6
; 0.00s
; (get-info :all-statistics)
; Final check that enough permissions have been taken
; Done splitting
(declare-const fvf@312 $FVF<Bool>)
(assert (=
  ($FVF.lookup_Ref__Boolean_value fvf@312 ($Seq.index $t@294 j@272))
  (and
    ($FVF.lookup_Ref__Boolean_value fvf@309 ($Seq.index $t@294 j@272))
    ($FVF.lookup_Ref__Boolean_value fvf@310 ($Seq.index $t@285 j@272)))))
(assert ($Set.equal
  ($FVF.domain_Ref__Boolean_value fvf@312)
  ($Set.singleton  ($Seq.index $t@294 j@272))))
; [exec]
; j := j + 1
; [eval] j + 1
(declare-const $k@313 $Perm)
(assert ($Perm.isValidVar $k@313))
(assert ($Perm.isReadVar $k@313 $Perm.Write))
(set-option :timeout 0)
(push) ; 6
(assert (not (or (= $k@313 $Perm.No) true)))
(check-sat)
; unsat
(pop) ; 6
; 0.00s
; (get-info :all-statistics)
(assert (< $k@313 $k@296))
; [eval] diz.Set__max > 0
(declare-const $k@314 $Perm)
(assert ($Perm.isValidVar $k@314))
(assert ($Perm.isReadVar $k@314 $Perm.Write))
(set-option :timeout 0)
(push) ; 6
(assert (not (or (= $k@314 $Perm.No) true)))
(check-sat)
; unsat
(pop) ; 6
; 0.00s
; (get-info :all-statistics)
(assert (< $k@314 $k@297))
; [eval] |diz.Set__contents| == diz.Set__max
; [eval] |diz.Set__contents|
(declare-const fvf@315 $FVF<Int>)
(declare-const fvf@316 $FVF<Int>)
(declare-const fvf@317 $FVF<$Seq<$Ref>>)
(declare-const fvf@318 $FVF<$Seq<$Ref>>)
(assert (= ($FVF.lookup_Set__max fvf@315 x@102) $t@288))
(assert ($Set.equal ($FVF.domain_Set__max fvf@315) ($Set.singleton  x@102)))
(assert (= ($FVF.lookup_Set__max fvf@316 diz@101) $t@295))
(assert ($Set.equal ($FVF.domain_Set__max fvf@316) ($Set.singleton  diz@101)))
(assert ($Seq.equal ($FVF.lookup_Set__contents fvf@317 x@102) $t@285))
(assert ($Set.equal ($FVF.domain_Set__contents fvf@317) ($Set.singleton  x@102)))
(assert ($Seq.equal ($FVF.lookup_Set__contents fvf@318 diz@101) $t@294))
(assert ($Set.equal ($FVF.domain_Set__contents fvf@318) ($Set.singleton  diz@101)))
(declare-const k@319 Int)
; [eval] (0 <= k) && (k < diz.Set__max)
; [eval] 0 <= k
(push) ; 6
(set-option :timeout 0)
(push) ; 7
(assert (not (not (<= 0 k@319))))
(check-sat)
; unknown
(pop) ; 7
; 0.00s
; (get-info :all-statistics)
(set-option :timeout 0)
(push) ; 7
(assert (not (<= 0 k@319)))
(check-sat)
; unknown
(pop) ; 7
; 0.00s
; (get-info :all-statistics)
(push) ; 7
; [then-branch 61] 0 <= k@319
(assert (<= 0 k@319))
; [eval] k < diz.Set__max
(set-option :timeout 0)
(push) ; 8
(assert (not (< $Perm.No (+ (ite (= diz@101 x@102) $k@300 $Perm.No) $k@296))))
(check-sat)
; unsat
(pop) ; 8
; 0.00s
; (get-info :all-statistics)
(declare-const fvf@320 $FVF<Int>)
(assert (implies
  (ite (= diz@101 x@102) (< $Perm.No $k@300) false)
  (=
    ($FVF.lookup_Set__max fvf@320 diz@101)
    ($FVF.lookup_Set__max fvf@315 diz@101))))
(assert (implies
  (< $Perm.No $k@296)
  (=
    ($FVF.lookup_Set__max fvf@320 diz@101)
    ($FVF.lookup_Set__max fvf@316 diz@101))))
(assert ($Set.equal ($FVF.domain_Set__max fvf@320) ($Set.singleton  diz@101)))
(pop) ; 7
(push) ; 7
; [else-branch 61] !0 <= k@319
(assert (not (<= 0 k@319)))
(pop) ; 7
(pop) ; 6
(assert ($Set.equal ($FVF.domain_Set__max fvf@320) ($Set.singleton  diz@101)))
(assert (implies
  (< $Perm.No $k@296)
  (=
    ($FVF.lookup_Set__max fvf@320 diz@101)
    ($FVF.lookup_Set__max fvf@316 diz@101))))
(assert (implies
  (ite (= diz@101 x@102) (< $Perm.No $k@300) false)
  (=
    ($FVF.lookup_Set__max fvf@320 diz@101)
    ($FVF.lookup_Set__max fvf@315 diz@101))))
(set-option :timeout 0)
(push) ; 6
(assert (not (not (and (<= 0 k@319) (< k@319 ($FVF.lookup_Set__max fvf@320 diz@101))))))
(check-sat)
; unknown
(pop) ; 6
; 0.01s
; (get-info :all-statistics)
(assert (and (<= 0 k@319) (< k@319 ($FVF.lookup_Set__max fvf@320 diz@101))))
; [eval] diz.Set__contents[k]
(set-option :timeout 0)
(push) ; 6
(assert (not (< $Perm.No (+ (ite (= diz@101 x@102) $k@301 $Perm.No) $k@297))))
(check-sat)
; unsat
(pop) ; 6
; 0.00s
; (get-info :all-statistics)
(declare-const fvf@321 $FVF<$Seq<$Ref>>)
(assert (implies
  (ite (= diz@101 x@102) (< $Perm.No $k@301) false)
  ($Seq.equal
    ($FVF.lookup_Set__contents fvf@321 diz@101)
    ($FVF.lookup_Set__contents fvf@317 diz@101))))
(assert (implies
  (< $Perm.No $k@297)
  ($Seq.equal
    ($FVF.lookup_Set__contents fvf@321 diz@101)
    ($FVF.lookup_Set__contents fvf@318 diz@101))))
(assert ($Set.equal ($FVF.domain_Set__contents fvf@321) ($Set.singleton  diz@101)))
(set-option :timeout 0)
(push) ; 6
(assert (not (forall (($x Int) ($y Int)) (!
  (implies
    (and
      (and (<= 0 $x) (< $x ($FVF.lookup_Set__max fvf@320 diz@101)))
      (and (<= 0 $y) (< $y ($FVF.lookup_Set__max fvf@320 diz@101)))
      (=
        ($Seq.index ($FVF.lookup_Set__contents fvf@321 diz@101) $x)
        ($Seq.index ($FVF.lookup_Set__contents fvf@321 diz@101) $y)))
    (= $x $y))
  :pattern (($Seq.index ($FVF.lookup_Set__contents fvf@321 diz@101) $x) ($Seq.index
    ($FVF.lookup_Set__contents fvf@321 diz@101)
    $y))))))
(check-sat)
; unsat
(pop) ; 6
; 0.00s
; (get-info :all-statistics)
(declare-fun invOf@322 ($Ref) Int)
(assert (forall (($r $Ref)) (!
  (implies
    (and
      (<= 0 (invOf@322 $r))
      (< (invOf@322 $r) ($FVF.lookup_Set__max fvf@320 diz@101)))
    (=
      ($Seq.index ($FVF.lookup_Set__contents fvf@321 diz@101) (invOf@322 $r))
      $r))
  :pattern ((invOf@322 $r)))))
(assert (forall ((k@319 Int)) (!
  (implies
    (and (<= 0 k@319) (< k@319 ($FVF.lookup_Set__max fvf@320 diz@101)))
    (=
      (invOf@322 ($Seq.index ($FVF.lookup_Set__contents fvf@321 diz@101) k@319))
      k@319))
  :pattern (($Seq.index ($FVF.lookup_Set__contents fvf@321 diz@101) k@319)))))
(declare-const fvf@323 $FVF<Bool>)
; Precomputing split data for Lookup(Set__contents,fvf@321,diz@101)[k@319].Ref__Boolean_value # W
(define-fun $permsTaken25 (($r $Ref)) $Perm
  ($Perm.min
    (ite
      (and
        (<= 0 (invOf@322 $r))
        (< (invOf@322 $r) ($FVF.lookup_Set__max fvf@320 diz@101)))
      $Perm.Write
      $Perm.No)
    (ite
      (= $r ($Seq.index ($FVF.lookup_Set__contents fvf@321 diz@101) k@319))
      (ite (= $r ($Seq.index $t@294 j@272)) $Perm.Write $Perm.No)
      $Perm.No)))
(define-fun $permsTaken26 (($r $Ref)) $Perm
  ($Perm.min
    (-
      (ite
        (and
          (<= 0 (invOf@322 $r))
          (< (invOf@322 $r) ($FVF.lookup_Set__max fvf@320 diz@101)))
        $Perm.Write
        $Perm.No)
      ($permsTaken25 $r))
    (ite
      (= $r ($Seq.index ($FVF.lookup_Set__contents fvf@321 diz@101) k@319))
      (-
        (ite
          (and (<= 0 (invOf@299 $r)) (< (invOf@299 $r) $t@295))
          $Perm.Write
          $Perm.No)
        ($permsTaken23 $r))
      $Perm.No)))
(define-fun $permsTaken27 (($r $Ref)) $Perm
  ($Perm.min
    (-
      (-
        (ite
          (and
            (<= 0 (invOf@322 $r))
            (< (invOf@322 $r) ($FVF.lookup_Set__max fvf@320 diz@101)))
          $Perm.Write
          $Perm.No)
        ($permsTaken25 $r))
      ($permsTaken26 $r))
    (ite
      (= $r ($Seq.index ($FVF.lookup_Set__contents fvf@321 diz@101) k@319))
      (ite (and (<= 0 (invOf@304 $r)) (< (invOf@304 $r) $t@288)) $k@303 $Perm.No)
      $Perm.No)))
; Done precomputing, updating quantified heap chunks
; Chunk depleted?
(set-option :timeout 500)
(push) ; 6
(assert (not (forall (($r $Ref)) (!
  (=
    (-
      (ite (= $r ($Seq.index $t@294 j@272)) $Perm.Write $Perm.No)
      ($permsTaken25 $r))
    $Perm.No)
  ))))
(check-sat)
; unknown
(pop) ; 6
; 0.01s
; (get-info :all-statistics)
; Enough permissions taken?
(set-option :timeout 500)
(push) ; 6
(assert (not (=
  (-
    (ite
      (and
        (<=
          0
          (invOf@322 ($Seq.index
            ($FVF.lookup_Set__contents fvf@321 diz@101)
            k@319)))
        (<
          (invOf@322 ($Seq.index
            ($FVF.lookup_Set__contents fvf@321 diz@101)
            k@319))
          ($FVF.lookup_Set__max fvf@320 diz@101)))
      $Perm.Write
      $Perm.No)
    ($permsTaken25 ($Seq.index ($FVF.lookup_Set__contents fvf@321 diz@101) k@319)))
  $Perm.No)))
(check-sat)
; unknown
(pop) ; 6
; 0.01s
; (get-info :all-statistics)
; Chunk depleted?
(set-option :timeout 500)
(push) ; 6
(assert (not (forall (($r $Ref)) (!
  (=
    (-
      (-
        (ite
          (and (<= 0 (invOf@299 $r)) (< (invOf@299 $r) $t@295))
          $Perm.Write
          $Perm.No)
        ($permsTaken23 $r))
      ($permsTaken26 $r))
    $Perm.No)
  ))))
(check-sat)
; unknown
(pop) ; 6
; 0.01s
; (get-info :all-statistics)
; Enough permissions taken?
(set-option :timeout 500)
(push) ; 6
(assert (not (=
  (-
    (-
      (ite
        (and
          (<=
            0
            (invOf@322 ($Seq.index
              ($FVF.lookup_Set__contents fvf@321 diz@101)
              k@319)))
          (<
            (invOf@322 ($Seq.index
              ($FVF.lookup_Set__contents fvf@321 diz@101)
              k@319))
            ($FVF.lookup_Set__max fvf@320 diz@101)))
        $Perm.Write
        $Perm.No)
      ($permsTaken25 ($Seq.index
        ($FVF.lookup_Set__contents fvf@321 diz@101)
        k@319)))
    ($permsTaken26 ($Seq.index ($FVF.lookup_Set__contents fvf@321 diz@101) k@319)))
  $Perm.No)))
(check-sat)
; unsat
(pop) ; 6
; 0.00s
; (get-info :all-statistics)
; Final check that enough permissions have been taken
; Done splitting
(assert (forall (($r $Ref)) (!
  (implies
    (and
      (ite
        (and (<= 0 (invOf@304 $r)) (< (invOf@304 $r) $t@288))
        (< $Perm.No $k@303)
        false)
      ($Set.in $r ($FVF.domain_Ref__Boolean_value fvf@323)))
    (=
      ($FVF.lookup_Ref__Boolean_value fvf@323 $r)
      ($FVF.lookup_Ref__Boolean_value $t@281 $r)))
  :pattern (($FVF.lookup_Ref__Boolean_value fvf@323 $r) (invOf@304 $r))
  :pattern (($FVF.lookup_Ref__Boolean_value $t@281 $r) (invOf@304 $r)))))
(assert (forall (($r $Ref)) (!
  (implies
    (and
      (<
        $Perm.No
        (-
          (ite
            (and (<= 0 (invOf@299 $r)) (< (invOf@299 $r) $t@295))
            $Perm.Write
            $Perm.No)
          ($permsTaken23 $r)))
      ($Set.in $r ($FVF.domain_Ref__Boolean_value fvf@323)))
    (=
      ($FVF.lookup_Ref__Boolean_value fvf@323 $r)
      ($FVF.lookup_Ref__Boolean_value $t@291 $r)))
  :pattern (($FVF.lookup_Ref__Boolean_value fvf@323 $r) (invOf@299 $r))
  :pattern (($FVF.lookup_Ref__Boolean_value $t@291 $r) (invOf@299 $r)))))
(assert (forall (($r $Ref)) (!
  (implies
    (and
      (= $r ($Seq.index $t@294 j@272))
      ($Set.in $r ($FVF.domain_Ref__Boolean_value fvf@323)))
    (=
      ($FVF.lookup_Ref__Boolean_value fvf@323 $r)
      ($FVF.lookup_Ref__Boolean_value fvf@312 $r)))
  :pattern (($FVF.lookup_Ref__Boolean_value fvf@323 $r))
  :pattern (($FVF.lookup_Ref__Boolean_value fvf@312 $r)))))
(assert (forall (($r $Ref)) (!
  (iff
    ($Set.in $r ($FVF.domain_Ref__Boolean_value fvf@323))
    (and
      (<= 0 (invOf@322 $r))
      (< (invOf@322 $r) ($FVF.lookup_Set__max fvf@320 diz@101))))
  :pattern (($Set.in $r ($FVF.domain_Ref__Boolean_value fvf@323))))))
; [eval] x != null
(declare-const $k@324 $Perm)
(assert ($Perm.isValidVar $k@324))
(assert ($Perm.isReadVar $k@324 $Perm.Write))
(set-option :timeout 0)
(push) ; 6
(assert (not (or (= $k@324 $Perm.No) true)))
(check-sat)
; unsat
(pop) ; 6
; 0.00s
; (get-info :all-statistics)
(assert (< $k@324 $k@300))
; [eval] x.Set__max > 0
(declare-const $k@325 $Perm)
(assert ($Perm.isValidVar $k@325))
(assert ($Perm.isReadVar $k@325 $Perm.Write))
(set-option :timeout 0)
(push) ; 6
(assert (not (or (= $k@325 $Perm.No) true)))
(check-sat)
; unsat
(pop) ; 6
; 0.00s
; (get-info :all-statistics)
(assert (< $k@325 $k@301))
; [eval] diz.Set__max > x.Set__max
; [eval] (j >= 0) && (j <= x.Set__max)
; [eval] j >= 0
(push) ; 6
(set-option :timeout 0)
(push) ; 7
(assert (not (not (>= (+ j@272 1) 0))))
(check-sat)
; unknown
(pop) ; 7
; 0.00s
; (get-info :all-statistics)
(set-option :timeout 0)
(push) ; 7
(assert (not (>= (+ j@272 1) 0)))
(check-sat)
; unsat
(pop) ; 7
; 0.00s
; (get-info :all-statistics)
(push) ; 7
; [then-branch 62] j@272 + 1 >= 0
(assert (>= (+ j@272 1) 0))
; [eval] j <= x.Set__max
(pop) ; 7
; [dead else-branch 62] !j@272 + 1 >= 0
(pop) ; 6
(set-option :timeout 0)
(push) ; 6
(assert (not (and (>= (+ j@272 1) 0) (<= (+ j@272 1) $t@288))))
(check-sat)
; unsat
(pop) ; 6
; 0.00s
; (get-info :all-statistics)
(assert (and (>= (+ j@272 1) 0) (<= (+ j@272 1) $t@288)))
(declare-const fvf@326 $FVF<Int>)
(declare-const fvf@327 $FVF<Int>)
(declare-const fvf@328 $FVF<$Seq<$Ref>>)
(declare-const fvf@329 $FVF<$Seq<$Ref>>)
(assert (= ($FVF.lookup_Set__max fvf@326 x@102) $t@288))
(assert ($Set.equal ($FVF.domain_Set__max fvf@326) ($Set.singleton  x@102)))
(assert (= ($FVF.lookup_Set__max fvf@327 diz@101) $t@295))
(assert ($Set.equal ($FVF.domain_Set__max fvf@327) ($Set.singleton  diz@101)))
(assert ($Seq.equal ($FVF.lookup_Set__contents fvf@328 x@102) $t@285))
(assert ($Set.equal ($FVF.domain_Set__contents fvf@328) ($Set.singleton  x@102)))
(assert ($Seq.equal ($FVF.lookup_Set__contents fvf@329 diz@101) $t@294))
(assert ($Set.equal ($FVF.domain_Set__contents fvf@329) ($Set.singleton  diz@101)))
(declare-const k@330 Int)
; [eval] (0 <= k) && (k < x.Set__max)
; [eval] 0 <= k
(push) ; 6
(set-option :timeout 0)
(push) ; 7
(assert (not (not (<= 0 k@330))))
(check-sat)
; unknown
(pop) ; 7
; 0.00s
; (get-info :all-statistics)
(set-option :timeout 0)
(push) ; 7
(assert (not (<= 0 k@330)))
(check-sat)
; unknown
(pop) ; 7
; 0.00s
; (get-info :all-statistics)
(push) ; 7
; [then-branch 63] 0 <= k@330
(assert (<= 0 k@330))
; [eval] k < x.Set__max
(set-option :timeout 0)
(push) ; 8
(assert (not (< $Perm.No (+ $k@300 (ite (= x@102 diz@101) $k@296 $Perm.No)))))
(check-sat)
; unsat
(pop) ; 8
; 0.00s
; (get-info :all-statistics)
(declare-const fvf@331 $FVF<Int>)
(assert (implies
  (< $Perm.No $k@300)
  (= ($FVF.lookup_Set__max fvf@331 x@102) ($FVF.lookup_Set__max fvf@326 x@102))))
(assert (implies
  (ite (= x@102 diz@101) (< $Perm.No $k@296) false)
  (= ($FVF.lookup_Set__max fvf@331 x@102) ($FVF.lookup_Set__max fvf@327 x@102))))
(assert ($Set.equal ($FVF.domain_Set__max fvf@331) ($Set.singleton  x@102)))
(pop) ; 7
(push) ; 7
; [else-branch 63] !0 <= k@330
(assert (not (<= 0 k@330)))
(pop) ; 7
(pop) ; 6
(assert ($Set.equal ($FVF.domain_Set__max fvf@331) ($Set.singleton  x@102)))
(assert (implies
  (ite (= x@102 diz@101) (< $Perm.No $k@296) false)
  (= ($FVF.lookup_Set__max fvf@331 x@102) ($FVF.lookup_Set__max fvf@327 x@102))))
(assert (implies
  (< $Perm.No $k@300)
  (= ($FVF.lookup_Set__max fvf@331 x@102) ($FVF.lookup_Set__max fvf@326 x@102))))
(set-option :timeout 0)
(push) ; 6
(assert (not (not (and (<= 0 k@330) (< k@330 ($FVF.lookup_Set__max fvf@331 x@102))))))
(check-sat)
; unknown
(pop) ; 6
; 0.01s
; (get-info :all-statistics)
(assert (and (<= 0 k@330) (< k@330 ($FVF.lookup_Set__max fvf@331 x@102))))
(declare-const $k@332 $Perm)
(assert ($Perm.isValidVar $k@332))
(assert ($Perm.isReadVar $k@332 $Perm.Write))
(set-option :timeout 0)
(push) ; 6
(assert (not (or (= $k@332 $Perm.No) true)))
(check-sat)
; unsat
(pop) ; 6
; 0.00s
; (get-info :all-statistics)
; [eval] x.Set__contents[k]
(set-option :timeout 0)
(push) ; 6
(assert (not (< $Perm.No (+ $k@301 (ite (= x@102 diz@101) $k@297 $Perm.No)))))
(check-sat)
; unsat
(pop) ; 6
; 0.00s
; (get-info :all-statistics)
(declare-const fvf@333 $FVF<$Seq<$Ref>>)
(assert (implies
  (< $Perm.No $k@301)
  ($Seq.equal
    ($FVF.lookup_Set__contents fvf@333 x@102)
    ($FVF.lookup_Set__contents fvf@328 x@102))))
(assert (implies
  (ite (= x@102 diz@101) (< $Perm.No $k@297) false)
  ($Seq.equal
    ($FVF.lookup_Set__contents fvf@333 x@102)
    ($FVF.lookup_Set__contents fvf@329 x@102))))
(assert ($Set.equal ($FVF.domain_Set__contents fvf@333) ($Set.singleton  x@102)))
(set-option :timeout 0)
(push) ; 6
(assert (not (forall (($x Int) ($y Int)) (!
  (implies
    (and
      (and (<= 0 $x) (< $x ($FVF.lookup_Set__max fvf@331 x@102)))
      (and (<= 0 $y) (< $y ($FVF.lookup_Set__max fvf@331 x@102)))
      (=
        ($Seq.index ($FVF.lookup_Set__contents fvf@333 x@102) $x)
        ($Seq.index ($FVF.lookup_Set__contents fvf@333 x@102) $y)))
    (= $x $y))
  :pattern (($Seq.index ($FVF.lookup_Set__contents fvf@333 x@102) $x) ($Seq.index
    ($FVF.lookup_Set__contents fvf@333 x@102)
    $y))))))
(check-sat)
; unsat
(pop) ; 6
; 0.00s
; (get-info :all-statistics)
(declare-fun invOf@334 ($Ref) Int)
(assert (forall (($r $Ref)) (!
  (implies
    (and
      (<= 0 (invOf@334 $r))
      (< (invOf@334 $r) ($FVF.lookup_Set__max fvf@331 x@102)))
    (= ($Seq.index ($FVF.lookup_Set__contents fvf@333 x@102) (invOf@334 $r)) $r))
  :pattern ((invOf@334 $r)))))
(assert (forall ((k@330 Int)) (!
  (implies
    (and (<= 0 k@330) (< k@330 ($FVF.lookup_Set__max fvf@331 x@102)))
    (=
      (invOf@334 ($Seq.index ($FVF.lookup_Set__contents fvf@333 x@102) k@330))
      k@330))
  :pattern (($Seq.index ($FVF.lookup_Set__contents fvf@333 x@102) k@330)))))
(declare-const fvf@335 $FVF<Bool>)
; Precomputing split data for Lookup(Set__contents,fvf@333,x@102)[k@330].Ref__Boolean_value # $k@332
(define-fun $permsTaken28 (($r $Ref)) $Perm
  ($Perm.min
    (ite
      (and
        (<= 0 (invOf@334 $r))
        (< (invOf@334 $r) ($FVF.lookup_Set__max fvf@331 x@102)))
      $k@332
      $Perm.No)
    (ite
      (= $r ($Seq.index ($FVF.lookup_Set__contents fvf@333 x@102) k@330))
      (-
        (ite (= $r ($Seq.index $t@294 j@272)) $Perm.Write $Perm.No)
        ($permsTaken25 $r))
      $Perm.No)))
(define-fun $permsTaken29 (($r $Ref)) $Perm
  ($Perm.min
    (-
      (ite
        (and
          (<= 0 (invOf@334 $r))
          (< (invOf@334 $r) ($FVF.lookup_Set__max fvf@331 x@102)))
        $k@332
        $Perm.No)
      ($permsTaken28 $r))
    (ite
      (= $r ($Seq.index ($FVF.lookup_Set__contents fvf@333 x@102) k@330))
      (-
        (-
          (ite
            (and (<= 0 (invOf@299 $r)) (< (invOf@299 $r) $t@295))
            $Perm.Write
            $Perm.No)
          ($permsTaken23 $r))
        ($permsTaken26 $r))
      $Perm.No)))
(define-fun $permsTaken30 (($r $Ref)) $Perm
  ($Perm.min
    (-
      (-
        (ite
          (and
            (<= 0 (invOf@334 $r))
            (< (invOf@334 $r) ($FVF.lookup_Set__max fvf@331 x@102)))
          $k@332
          $Perm.No)
        ($permsTaken28 $r))
      ($permsTaken29 $r))
    (ite
      (= $r ($Seq.index ($FVF.lookup_Set__contents fvf@333 x@102) k@330))
      (ite (and (<= 0 (invOf@304 $r)) (< (invOf@304 $r) $t@288)) $k@303 $Perm.No)
      $Perm.No)))
; Done precomputing, updating quantified heap chunks
; Constrain original permissions $k@332
(assert (forall (($r $Ref)) (!
  (implies
    (not
      (=
        (-
          (ite (= $r ($Seq.index $t@294 j@272)) $Perm.Write $Perm.No)
          ($permsTaken25 $r))
        $Perm.No))
    (<
      (ite
        (and
          (<= 0 (invOf@334 $r))
          (< (invOf@334 $r) ($FVF.lookup_Set__max fvf@331 x@102)))
        $k@332
        $Perm.No)
      (-
        (ite (= $r ($Seq.index $t@294 j@272)) $Perm.Write $Perm.No)
        ($permsTaken25 $r))))
  :pattern ((invOf@334 $r))
  :pattern ((invOf@334 $r)))))
; Enough permissions taken?
(set-option :timeout 500)
(push) ; 6
(assert (not (=
  (-
    (ite
      (and
        (<=
          0
          (invOf@334 ($Seq.index ($FVF.lookup_Set__contents fvf@333 x@102) k@330)))
        (<
          (invOf@334 ($Seq.index ($FVF.lookup_Set__contents fvf@333 x@102) k@330))
          ($FVF.lookup_Set__max fvf@331 x@102)))
      $k@332
      $Perm.No)
    ($permsTaken28 ($Seq.index ($FVF.lookup_Set__contents fvf@333 x@102) k@330)))
  $Perm.No)))
(check-sat)
; unknown
(pop) ; 6
; 0.01s
; (get-info :all-statistics)
; Constrain original permissions $k@332
(assert (forall (($r $Ref)) (!
  (implies
    (not
      (=
        (-
          (-
            (ite
              (and (<= 0 (invOf@299 $r)) (< (invOf@299 $r) $t@295))
              $Perm.Write
              $Perm.No)
            ($permsTaken23 $r))
          ($permsTaken26 $r))
        $Perm.No))
    (<
      (ite
        (and
          (<= 0 (invOf@334 $r))
          (< (invOf@334 $r) ($FVF.lookup_Set__max fvf@331 x@102)))
        $k@332
        $Perm.No)
      (-
        (-
          (ite
            (and (<= 0 (invOf@299 $r)) (< (invOf@299 $r) $t@295))
            $Perm.Write
            $Perm.No)
          ($permsTaken23 $r))
        ($permsTaken26 $r))))
  :pattern ((invOf@299 $r))
  :pattern ((invOf@299 $r))
  :pattern ((invOf@334 $r))
  :pattern ((invOf@334 $r))
  :pattern ((invOf@299 $r))
  :pattern ((invOf@299 $r)))))
; Enough permissions taken?
(set-option :timeout 500)
(push) ; 6
(assert (not (=
  (-
    (-
      (ite
        (and
          (<=
            0
            (invOf@334 ($Seq.index
              ($FVF.lookup_Set__contents fvf@333 x@102)
              k@330)))
          (<
            (invOf@334 ($Seq.index
              ($FVF.lookup_Set__contents fvf@333 x@102)
              k@330))
            ($FVF.lookup_Set__max fvf@331 x@102)))
        $k@332
        $Perm.No)
      ($permsTaken28 ($Seq.index ($FVF.lookup_Set__contents fvf@333 x@102) k@330)))
    ($permsTaken29 ($Seq.index ($FVF.lookup_Set__contents fvf@333 x@102) k@330)))
  $Perm.No)))
(check-sat)
; unknown
(pop) ; 6
; 0.03s
; (get-info :all-statistics)
; Constrain original permissions $k@332
(assert (forall (($r $Ref)) (!
  (implies
    (not
      (=
        (ite
          (and (<= 0 (invOf@304 $r)) (< (invOf@304 $r) $t@288))
          $k@303
          $Perm.No)
        $Perm.No))
    (ite
      (and (<= 0 (invOf@304 $r)) (< (invOf@304 $r) $t@288))
      (<
        (ite
          (and
            (<= 0 (invOf@334 $r))
            (< (invOf@334 $r) ($FVF.lookup_Set__max fvf@331 x@102)))
          $k@332
          $Perm.No)
        $k@303)
      (<
        (ite
          (and
            (<= 0 (invOf@334 $r))
            (< (invOf@334 $r) ($FVF.lookup_Set__max fvf@331 x@102)))
          $k@332
          $Perm.No)
        $Perm.No)))
  :pattern ((invOf@304 $r))
  :pattern ((invOf@304 $r))
  :pattern ((invOf@304 $r))
  :pattern ((invOf@304 $r))
  :pattern ((invOf@334 $r))
  :pattern ((invOf@334 $r))
  :pattern ((invOf@334 $r))
  :pattern ((invOf@334 $r)))))
; Enough permissions taken?
(set-option :timeout 500)
(push) ; 6
(assert (not (=
  (-
    (-
      (-
        (ite
          (and
            (<=
              0
              (invOf@334 ($Seq.index
                ($FVF.lookup_Set__contents fvf@333 x@102)
                k@330)))
            (<
              (invOf@334 ($Seq.index
                ($FVF.lookup_Set__contents fvf@333 x@102)
                k@330))
              ($FVF.lookup_Set__max fvf@331 x@102)))
          $k@332
          $Perm.No)
        ($permsTaken28 ($Seq.index
          ($FVF.lookup_Set__contents fvf@333 x@102)
          k@330)))
      ($permsTaken29 ($Seq.index ($FVF.lookup_Set__contents fvf@333 x@102) k@330)))
    ($permsTaken30 ($Seq.index ($FVF.lookup_Set__contents fvf@333 x@102) k@330)))
  $Perm.No)))
(check-sat)
; unsat
(pop) ; 6
; 0.01s
; (get-info :all-statistics)
; Final check that enough permissions have been taken
; Done splitting
(assert (forall (($r $Ref)) (!
  (implies
    (and
      (ite
        (and (<= 0 (invOf@304 $r)) (< (invOf@304 $r) $t@288))
        (< $Perm.No $k@303)
        false)
      ($Set.in $r ($FVF.domain_Ref__Boolean_value fvf@335)))
    (=
      ($FVF.lookup_Ref__Boolean_value fvf@335 $r)
      ($FVF.lookup_Ref__Boolean_value $t@281 $r)))
  :pattern (($FVF.lookup_Ref__Boolean_value fvf@335 $r) (invOf@304 $r))
  :pattern (($FVF.lookup_Ref__Boolean_value $t@281 $r) (invOf@304 $r)))))
(assert (forall (($r $Ref)) (!
  (implies
    (and
      (<
        $Perm.No
        (-
          (-
            (ite
              (and (<= 0 (invOf@299 $r)) (< (invOf@299 $r) $t@295))
              $Perm.Write
              $Perm.No)
            ($permsTaken23 $r))
          ($permsTaken26 $r)))
      ($Set.in $r ($FVF.domain_Ref__Boolean_value fvf@335)))
    (=
      ($FVF.lookup_Ref__Boolean_value fvf@335 $r)
      ($FVF.lookup_Ref__Boolean_value $t@291 $r)))
  :pattern (($FVF.lookup_Ref__Boolean_value fvf@335 $r) (invOf@299 $r))
  :pattern (($FVF.lookup_Ref__Boolean_value $t@291 $r) (invOf@299 $r)))))
(assert (forall (($r $Ref)) (!
  (implies
    (and
      (<
        $Perm.No
        (-
          (ite (= $r ($Seq.index $t@294 j@272)) $Perm.Write $Perm.No)
          ($permsTaken25 $r)))
      ($Set.in $r ($FVF.domain_Ref__Boolean_value fvf@335)))
    (=
      ($FVF.lookup_Ref__Boolean_value fvf@335 $r)
      ($FVF.lookup_Ref__Boolean_value fvf@312 $r)))
  :pattern (($FVF.lookup_Ref__Boolean_value fvf@335 $r))
  :pattern (($FVF.lookup_Ref__Boolean_value fvf@312 $r)))))
(assert (forall (($r $Ref)) (!
  (iff
    ($Set.in $r ($FVF.domain_Ref__Boolean_value fvf@335))
    (and
      (<= 0 (invOf@334 $r))
      (< (invOf@334 $r) ($FVF.lookup_Set__max fvf@331 x@102))))
  :pattern (($Set.in $r ($FVF.domain_Ref__Boolean_value fvf@335))))))
; [eval] (forall k: Int :: (0 <= k) && (k < j) ==> (diz.Set__contents[k].Ref__Boolean_value == diz.Set__contents[k].Ref__Boolean_value && x.Set__contents[k].Ref__Boolean_value))
(declare-const k@336 Int)
(push) ; 6
; [eval] (0 <= k) && (k < j) ==> (diz.Set__contents[k].Ref__Boolean_value == diz.Set__contents[k].Ref__Boolean_value && x.Set__contents[k].Ref__Boolean_value)
; [eval] (0 <= k) && (k < j)
; [eval] 0 <= k
(push) ; 7
(set-option :timeout 0)
(push) ; 8
(assert (not (not (<= 0 k@336))))
(check-sat)
; unknown
(pop) ; 8
; 0.03s
; (get-info :all-statistics)
(set-option :timeout 0)
(push) ; 8
(assert (not (<= 0 k@336)))
(check-sat)
; unknown
(pop) ; 8
; 0.03s
; (get-info :all-statistics)
(push) ; 8
; [then-branch 64] 0 <= k@336
(assert (<= 0 k@336))
; [eval] k < j
(pop) ; 8
(push) ; 8
; [else-branch 64] !0 <= k@336
(assert (not (<= 0 k@336)))
(pop) ; 8
(pop) ; 7
(push) ; 7
(set-option :timeout 0)
(push) ; 8
(assert (not (not (and (<= 0 k@336) (< k@336 (+ j@272 1))))))
(check-sat)
; unknown
(pop) ; 8
; 0.02s
; (get-info :all-statistics)
(set-option :timeout 0)
(push) ; 8
(assert (not (and (<= 0 k@336) (< k@336 (+ j@272 1)))))
(check-sat)
; unknown
(pop) ; 8
; 0.03s
; (get-info :all-statistics)
(push) ; 8
; [then-branch 65] 0 <= k@336 && k@336 < j@272 + 1
(assert (and (<= 0 k@336) (< k@336 (+ j@272 1))))
; [eval] diz.Set__contents[k].Ref__Boolean_value == diz.Set__contents[k].Ref__Boolean_value && x.Set__contents[k].Ref__Boolean_value
; [eval] diz.Set__contents[k]
(set-option :timeout 0)
(push) ; 9
(assert (not (not (= ($Seq.index $t@294 k@336) $Ref.null))))
(check-sat)
; unsat
(pop) ; 9
; 0.00s
; (get-info :all-statistics)
(set-option :timeout 0)
(push) ; 9
(assert (not (<
  $Perm.No
  (+
    (+
      (ite
        (and
          (<= 0 (invOf@304 ($Seq.index $t@294 k@336)))
          (< (invOf@304 ($Seq.index $t@294 k@336)) $t@288))
        $k@303
        $Perm.No)
      (-
        (ite
          (and
            (<= 0 (invOf@299 ($Seq.index $t@294 k@336)))
            (< (invOf@299 ($Seq.index $t@294 k@336)) $t@295))
          $Perm.Write
          $Perm.No)
        ($permsTaken23 ($Seq.index $t@294 k@336))))
    (ite
      (= ($Seq.index $t@294 k@336) ($Seq.index $t@294 j@272))
      $Perm.Write
      $Perm.No)))))
(check-sat)
; unsat
(pop) ; 9
; 0.01s
; (get-info :all-statistics)
(declare-const fvf@337 $FVF<Bool>)
(assert (forall (($r $Ref)) (!
  (implies
    (and
      (ite
        (and (<= 0 (invOf@304 $r)) (< (invOf@304 $r) $t@288))
        (< $Perm.No $k@303)
        false)
      ($Set.in $r ($FVF.domain_Ref__Boolean_value fvf@337)))
    (=
      ($FVF.lookup_Ref__Boolean_value fvf@337 $r)
      ($FVF.lookup_Ref__Boolean_value $t@281 $r)))
  :pattern (($FVF.lookup_Ref__Boolean_value fvf@337 $r) (invOf@304 $r))
  :pattern (($FVF.lookup_Ref__Boolean_value $t@281 $r) (invOf@304 $r)))))
(assert (forall (($r $Ref)) (!
  (implies
    (and
      (<
        $Perm.No
        (-
          (ite
            (and (<= 0 (invOf@299 $r)) (< (invOf@299 $r) $t@295))
            $Perm.Write
            $Perm.No)
          ($permsTaken23 $r)))
      ($Set.in $r ($FVF.domain_Ref__Boolean_value fvf@337)))
    (=
      ($FVF.lookup_Ref__Boolean_value fvf@337 $r)
      ($FVF.lookup_Ref__Boolean_value $t@291 $r)))
  :pattern (($FVF.lookup_Ref__Boolean_value fvf@337 $r) (invOf@299 $r))
  :pattern (($FVF.lookup_Ref__Boolean_value $t@291 $r) (invOf@299 $r)))))
(assert (forall (($r $Ref)) (!
  (implies
    (and
      (= $r ($Seq.index $t@294 j@272))
      ($Set.in $r ($FVF.domain_Ref__Boolean_value fvf@337)))
    (=
      ($FVF.lookup_Ref__Boolean_value fvf@337 $r)
      ($FVF.lookup_Ref__Boolean_value fvf@312 $r)))
  :pattern (($FVF.lookup_Ref__Boolean_value fvf@337 $r))
  :pattern (($FVF.lookup_Ref__Boolean_value fvf@312 $r)))))
(assert (forall ((k@336 Int)) (!
  (iff
    ($Set.in ($Seq.index $t@294 k@336) ($FVF.domain_Ref__Boolean_value fvf@337))
    (and (and (<= 0 k@336) (< k@336 (+ j@272 1))) (not (<= $t@116 $t@123))))
  :pattern (($Set.in
    ($Seq.index $t@294 k@336)
    ($FVF.domain_Ref__Boolean_value fvf@337))))))
; [eval] diz.Set__contents[k].Ref__Boolean_value && x.Set__contents[k].Ref__Boolean_value
; [eval] diz.Set__contents[k]
(set-option :timeout 0)
(push) ; 9
(assert (not (not (= ($Seq.index $t@294 k@336) $Ref.null))))
(check-sat)
; unsat
(pop) ; 9
; 0.00s
; (get-info :all-statistics)
(set-option :timeout 0)
(push) ; 9
(assert (not (<
  $Perm.No
  (+
    (+
      (ite
        (and
          (<= 0 (invOf@304 ($Seq.index $t@294 k@336)))
          (< (invOf@304 ($Seq.index $t@294 k@336)) $t@288))
        $k@303
        $Perm.No)
      (-
        (ite
          (and
            (<= 0 (invOf@299 ($Seq.index $t@294 k@336)))
            (< (invOf@299 ($Seq.index $t@294 k@336)) $t@295))
          $Perm.Write
          $Perm.No)
        ($permsTaken23 ($Seq.index $t@294 k@336))))
    (ite
      (= ($Seq.index $t@294 k@336) ($Seq.index $t@294 j@272))
      $Perm.Write
      $Perm.No)))))
(check-sat)
; unsat
(pop) ; 9
; 0.01s
; (get-info :all-statistics)
(declare-const fvf@338 $FVF<Bool>)
(push) ; 9
(set-option :timeout 0)
(push) ; 10
(assert (not (not ($FVF.lookup_Ref__Boolean_value fvf@337 ($Seq.index $t@294 k@336)))))
(check-sat)
; unknown
(pop) ; 10
; 0.06s
; (get-info :all-statistics)
(set-option :timeout 0)
(push) ; 10
(assert (not ($FVF.lookup_Ref__Boolean_value fvf@337 ($Seq.index $t@294 k@336))))
(check-sat)
; unknown
(pop) ; 10
; 0.05s
; (get-info :all-statistics)
(push) ; 10
; [then-branch 66] Lookup(Ref__Boolean_value,fvf@337,$t@294[k@336])
(assert ($FVF.lookup_Ref__Boolean_value fvf@337 ($Seq.index $t@294 k@336)))
; [eval] x.Set__contents[k]
(set-option :timeout 0)
(push) ; 11
(assert (not (not (= ($Seq.index $t@285 k@336) $Ref.null))))
(check-sat)
; unsat
(pop) ; 11
; 0.00s
; (get-info :all-statistics)
(set-option :timeout 0)
(push) ; 11
(assert (not (<
  $Perm.No
  (+
    (+
      (ite
        (and
          (<= 0 (invOf@304 ($Seq.index $t@285 k@336)))
          (< (invOf@304 ($Seq.index $t@285 k@336)) $t@288))
        $k@303
        $Perm.No)
      (-
        (ite
          (and
            (<= 0 (invOf@299 ($Seq.index $t@285 k@336)))
            (< (invOf@299 ($Seq.index $t@285 k@336)) $t@295))
          $Perm.Write
          $Perm.No)
        ($permsTaken23 ($Seq.index $t@285 k@336))))
    (ite
      (= ($Seq.index $t@285 k@336) ($Seq.index $t@294 j@272))
      $Perm.Write
      $Perm.No)))))
(check-sat)
; unsat
(pop) ; 11
; 0.01s
; (get-info :all-statistics)
(declare-const fvf@339 $FVF<Bool>)
(assert (forall (($r $Ref)) (!
  (implies
    (and
      (ite
        (and (<= 0 (invOf@304 $r)) (< (invOf@304 $r) $t@288))
        (< $Perm.No $k@303)
        false)
      ($Set.in $r ($FVF.domain_Ref__Boolean_value fvf@339)))
    (=
      ($FVF.lookup_Ref__Boolean_value fvf@339 $r)
      ($FVF.lookup_Ref__Boolean_value $t@281 $r)))
  :pattern (($FVF.lookup_Ref__Boolean_value fvf@339 $r) (invOf@304 $r))
  :pattern (($FVF.lookup_Ref__Boolean_value $t@281 $r) (invOf@304 $r)))))
(assert (forall (($r $Ref)) (!
  (implies
    (and
      (<
        $Perm.No
        (-
          (ite
            (and (<= 0 (invOf@299 $r)) (< (invOf@299 $r) $t@295))
            $Perm.Write
            $Perm.No)
          ($permsTaken23 $r)))
      ($Set.in $r ($FVF.domain_Ref__Boolean_value fvf@339)))
    (=
      ($FVF.lookup_Ref__Boolean_value fvf@339 $r)
      ($FVF.lookup_Ref__Boolean_value $t@291 $r)))
  :pattern (($FVF.lookup_Ref__Boolean_value fvf@339 $r) (invOf@299 $r))
  :pattern (($FVF.lookup_Ref__Boolean_value $t@291 $r) (invOf@299 $r)))))
(assert (forall (($r $Ref)) (!
  (implies
    (and
      (= $r ($Seq.index $t@294 j@272))
      ($Set.in $r ($FVF.domain_Ref__Boolean_value fvf@339)))
    (=
      ($FVF.lookup_Ref__Boolean_value fvf@339 $r)
      ($FVF.lookup_Ref__Boolean_value fvf@312 $r)))
  :pattern (($FVF.lookup_Ref__Boolean_value fvf@339 $r))
  :pattern (($FVF.lookup_Ref__Boolean_value fvf@312 $r)))))
(assert (forall ((k@336 Int)) (!
  (iff
    ($Set.in ($Seq.index $t@285 k@336) ($FVF.domain_Ref__Boolean_value fvf@339))
    (and
      ($FVF.lookup_Ref__Boolean_value fvf@337 ($Seq.index $t@294 k@336))
      (and (<= 0 k@336) (< k@336 (+ j@272 1)))
      (not (<= $t@116 $t@123))))
  :pattern (($Set.in
    ($Seq.index $t@285 k@336)
    ($FVF.domain_Ref__Boolean_value fvf@339))))))
(pop) ; 10
(push) ; 10
; [else-branch 66] !Lookup(Ref__Boolean_value,fvf@337,$t@294[k@336])
(assert (not ($FVF.lookup_Ref__Boolean_value fvf@337 ($Seq.index $t@294 k@336))))
(pop) ; 10
(pop) ; 9
(assert (forall ((k@336 Int)) (!
  (iff
    ($Set.in ($Seq.index $t@285 k@336) ($FVF.domain_Ref__Boolean_value fvf@339))
    (and
      ($FVF.lookup_Ref__Boolean_value fvf@337 ($Seq.index $t@294 k@336))
      (and (<= 0 k@336) (< k@336 (+ j@272 1)))
      (not (<= $t@116 $t@123))))
  :pattern (($Set.in
    ($Seq.index $t@285 k@336)
    ($FVF.domain_Ref__Boolean_value fvf@339))))))
(assert (forall (($r $Ref)) (!
  (implies
    (and
      (= $r ($Seq.index $t@294 j@272))
      ($Set.in $r ($FVF.domain_Ref__Boolean_value fvf@339)))
    (=
      ($FVF.lookup_Ref__Boolean_value fvf@339 $r)
      ($FVF.lookup_Ref__Boolean_value fvf@312 $r)))
  :pattern (($FVF.lookup_Ref__Boolean_value fvf@339 $r))
  :pattern (($FVF.lookup_Ref__Boolean_value fvf@312 $r)))))
(assert (forall (($r $Ref)) (!
  (implies
    (and
      (<
        $Perm.No
        (-
          (ite
            (and (<= 0 (invOf@299 $r)) (< (invOf@299 $r) $t@295))
            $Perm.Write
            $Perm.No)
          ($permsTaken23 $r)))
      ($Set.in $r ($FVF.domain_Ref__Boolean_value fvf@339)))
    (=
      ($FVF.lookup_Ref__Boolean_value fvf@339 $r)
      ($FVF.lookup_Ref__Boolean_value $t@291 $r)))
  :pattern (($FVF.lookup_Ref__Boolean_value fvf@339 $r) (invOf@299 $r))
  :pattern (($FVF.lookup_Ref__Boolean_value $t@291 $r) (invOf@299 $r)))))
(assert (forall (($r $Ref)) (!
  (implies
    (and
      (ite
        (and (<= 0 (invOf@304 $r)) (< (invOf@304 $r) $t@288))
        (< $Perm.No $k@303)
        false)
      ($Set.in $r ($FVF.domain_Ref__Boolean_value fvf@339)))
    (=
      ($FVF.lookup_Ref__Boolean_value fvf@339 $r)
      ($FVF.lookup_Ref__Boolean_value $t@281 $r)))
  :pattern (($FVF.lookup_Ref__Boolean_value fvf@339 $r) (invOf@304 $r))
  :pattern (($FVF.lookup_Ref__Boolean_value $t@281 $r) (invOf@304 $r)))))
(pop) ; 8
(push) ; 8
; [else-branch 65] !0 <= k@336 && k@336 < j@272 + 1
(assert (not (and (<= 0 k@336) (< k@336 (+ j@272 1)))))
(pop) ; 8
(pop) ; 7
(assert (forall (($r $Ref)) (!
  (implies
    (and
      (ite
        (and (<= 0 (invOf@304 $r)) (< (invOf@304 $r) $t@288))
        (< $Perm.No $k@303)
        false)
      ($Set.in $r ($FVF.domain_Ref__Boolean_value fvf@339)))
    (=
      ($FVF.lookup_Ref__Boolean_value fvf@339 $r)
      ($FVF.lookup_Ref__Boolean_value $t@281 $r)))
  :pattern (($FVF.lookup_Ref__Boolean_value fvf@339 $r) (invOf@304 $r))
  :pattern (($FVF.lookup_Ref__Boolean_value $t@281 $r) (invOf@304 $r)))))
(assert (forall (($r $Ref)) (!
  (implies
    (and
      (<
        $Perm.No
        (-
          (ite
            (and (<= 0 (invOf@299 $r)) (< (invOf@299 $r) $t@295))
            $Perm.Write
            $Perm.No)
          ($permsTaken23 $r)))
      ($Set.in $r ($FVF.domain_Ref__Boolean_value fvf@339)))
    (=
      ($FVF.lookup_Ref__Boolean_value fvf@339 $r)
      ($FVF.lookup_Ref__Boolean_value $t@291 $r)))
  :pattern (($FVF.lookup_Ref__Boolean_value fvf@339 $r) (invOf@299 $r))
  :pattern (($FVF.lookup_Ref__Boolean_value $t@291 $r) (invOf@299 $r)))))
(assert (forall (($r $Ref)) (!
  (implies
    (and
      (= $r ($Seq.index $t@294 j@272))
      ($Set.in $r ($FVF.domain_Ref__Boolean_value fvf@339)))
    (=
      ($FVF.lookup_Ref__Boolean_value fvf@339 $r)
      ($FVF.lookup_Ref__Boolean_value fvf@312 $r)))
  :pattern (($FVF.lookup_Ref__Boolean_value fvf@339 $r))
  :pattern (($FVF.lookup_Ref__Boolean_value fvf@312 $r)))))
(assert (forall ((k@336 Int)) (!
  (iff
    ($Set.in ($Seq.index $t@285 k@336) ($FVF.domain_Ref__Boolean_value fvf@339))
    (and
      ($FVF.lookup_Ref__Boolean_value fvf@337 ($Seq.index $t@294 k@336))
      (and (<= 0 k@336) (< k@336 (+ j@272 1)))
      (not (<= $t@116 $t@123))))
  :pattern (($Set.in
    ($Seq.index $t@285 k@336)
    ($FVF.domain_Ref__Boolean_value fvf@339))))))
(assert (forall ((k@336 Int)) (!
  (iff
    ($Set.in ($Seq.index $t@294 k@336) ($FVF.domain_Ref__Boolean_value fvf@337))
    (and (and (<= 0 k@336) (< k@336 (+ j@272 1))) (not (<= $t@116 $t@123))))
  :pattern (($Set.in
    ($Seq.index $t@294 k@336)
    ($FVF.domain_Ref__Boolean_value fvf@337))))))
(assert (forall (($r $Ref)) (!
  (implies
    (and
      (= $r ($Seq.index $t@294 j@272))
      ($Set.in $r ($FVF.domain_Ref__Boolean_value fvf@337)))
    (=
      ($FVF.lookup_Ref__Boolean_value fvf@337 $r)
      ($FVF.lookup_Ref__Boolean_value fvf@312 $r)))
  :pattern (($FVF.lookup_Ref__Boolean_value fvf@337 $r))
  :pattern (($FVF.lookup_Ref__Boolean_value fvf@312 $r)))))
(assert (forall (($r $Ref)) (!
  (implies
    (and
      (<
        $Perm.No
        (-
          (ite
            (and (<= 0 (invOf@299 $r)) (< (invOf@299 $r) $t@295))
            $Perm.Write
            $Perm.No)
          ($permsTaken23 $r)))
      ($Set.in $r ($FVF.domain_Ref__Boolean_value fvf@337)))
    (=
      ($FVF.lookup_Ref__Boolean_value fvf@337 $r)
      ($FVF.lookup_Ref__Boolean_value $t@291 $r)))
  :pattern (($FVF.lookup_Ref__Boolean_value fvf@337 $r) (invOf@299 $r))
  :pattern (($FVF.lookup_Ref__Boolean_value $t@291 $r) (invOf@299 $r)))))
(assert (forall (($r $Ref)) (!
  (implies
    (and
      (ite
        (and (<= 0 (invOf@304 $r)) (< (invOf@304 $r) $t@288))
        (< $Perm.No $k@303)
        false)
      ($Set.in $r ($FVF.domain_Ref__Boolean_value fvf@337)))
    (=
      ($FVF.lookup_Ref__Boolean_value fvf@337 $r)
      ($FVF.lookup_Ref__Boolean_value $t@281 $r)))
  :pattern (($FVF.lookup_Ref__Boolean_value fvf@337 $r) (invOf@304 $r))
  :pattern (($FVF.lookup_Ref__Boolean_value $t@281 $r) (invOf@304 $r)))))
(pop) ; 6
(assert (forall (($r $Ref)) (!
  (implies
    (and
      (ite
        (and (<= 0 (invOf@304 $r)) (< (invOf@304 $r) $t@288))
        (< $Perm.No $k@303)
        false)
      ($Set.in $r ($FVF.domain_Ref__Boolean_value fvf@339)))
    (=
      ($FVF.lookup_Ref__Boolean_value fvf@339 $r)
      ($FVF.lookup_Ref__Boolean_value $t@281 $r)))
  :pattern (($FVF.lookup_Ref__Boolean_value fvf@339 $r) (invOf@304 $r))
  :pattern (($FVF.lookup_Ref__Boolean_value $t@281 $r) (invOf@304 $r)))))
(assert (forall (($r $Ref)) (!
  (implies
    (and
      (<
        $Perm.No
        (-
          (ite
            (and (<= 0 (invOf@299 $r)) (< (invOf@299 $r) $t@295))
            $Perm.Write
            $Perm.No)
          ($permsTaken23 $r)))
      ($Set.in $r ($FVF.domain_Ref__Boolean_value fvf@339)))
    (=
      ($FVF.lookup_Ref__Boolean_value fvf@339 $r)
      ($FVF.lookup_Ref__Boolean_value $t@291 $r)))
  :pattern (($FVF.lookup_Ref__Boolean_value fvf@339 $r) (invOf@299 $r))
  :pattern (($FVF.lookup_Ref__Boolean_value $t@291 $r) (invOf@299 $r)))))
(assert (forall (($r $Ref)) (!
  (implies
    (and
      (= $r ($Seq.index $t@294 j@272))
      ($Set.in $r ($FVF.domain_Ref__Boolean_value fvf@339)))
    (=
      ($FVF.lookup_Ref__Boolean_value fvf@339 $r)
      ($FVF.lookup_Ref__Boolean_value fvf@312 $r)))
  :pattern (($FVF.lookup_Ref__Boolean_value fvf@339 $r))
  :pattern (($FVF.lookup_Ref__Boolean_value fvf@312 $r)))))
(assert (forall ((k@336 Int)) (!
  (iff
    ($Set.in ($Seq.index $t@285 k@336) ($FVF.domain_Ref__Boolean_value fvf@339))
    (and
      ($FVF.lookup_Ref__Boolean_value fvf@337 ($Seq.index $t@294 k@336))
      (and (<= 0 k@336) (< k@336 (+ j@272 1)))
      (not (<= $t@116 $t@123))))
  :pattern (($Set.in
    ($Seq.index $t@285 k@336)
    ($FVF.domain_Ref__Boolean_value fvf@339))))))
(assert (forall ((k@336 Int)) (!
  (iff
    ($Set.in ($Seq.index $t@294 k@336) ($FVF.domain_Ref__Boolean_value fvf@337))
    (and (and (<= 0 k@336) (< k@336 (+ j@272 1))) (not (<= $t@116 $t@123))))
  :pattern (($Set.in
    ($Seq.index $t@294 k@336)
    ($FVF.domain_Ref__Boolean_value fvf@337))))))
(assert (forall (($r $Ref)) (!
  (implies
    (and
      (= $r ($Seq.index $t@294 j@272))
      ($Set.in $r ($FVF.domain_Ref__Boolean_value fvf@337)))
    (=
      ($FVF.lookup_Ref__Boolean_value fvf@337 $r)
      ($FVF.lookup_Ref__Boolean_value fvf@312 $r)))
  :pattern (($FVF.lookup_Ref__Boolean_value fvf@337 $r))
  :pattern (($FVF.lookup_Ref__Boolean_value fvf@312 $r)))))
(assert (forall (($r $Ref)) (!
  (implies
    (and
      (<
        $Perm.No
        (-
          (ite
            (and (<= 0 (invOf@299 $r)) (< (invOf@299 $r) $t@295))
            $Perm.Write
            $Perm.No)
          ($permsTaken23 $r)))
      ($Set.in $r ($FVF.domain_Ref__Boolean_value fvf@337)))
    (=
      ($FVF.lookup_Ref__Boolean_value fvf@337 $r)
      ($FVF.lookup_Ref__Boolean_value $t@291 $r)))
  :pattern (($FVF.lookup_Ref__Boolean_value fvf@337 $r) (invOf@299 $r))
  :pattern (($FVF.lookup_Ref__Boolean_value $t@291 $r) (invOf@299 $r)))))
(assert (forall (($r $Ref)) (!
  (implies
    (and
      (ite
        (and (<= 0 (invOf@304 $r)) (< (invOf@304 $r) $t@288))
        (< $Perm.No $k@303)
        false)
      ($Set.in $r ($FVF.domain_Ref__Boolean_value fvf@337)))
    (=
      ($FVF.lookup_Ref__Boolean_value fvf@337 $r)
      ($FVF.lookup_Ref__Boolean_value $t@281 $r)))
  :pattern (($FVF.lookup_Ref__Boolean_value fvf@337 $r) (invOf@304 $r))
  :pattern (($FVF.lookup_Ref__Boolean_value $t@281 $r) (invOf@304 $r)))))
(set-option :timeout 0)
(push) ; 6
(assert (not (forall ((k@336 Int)) (!
  (implies
    (and (<= 0 k@336) (< k@336 (+ j@272 1)))
    (=
      ($FVF.lookup_Ref__Boolean_value fvf@337 ($Seq.index $t@294 k@336))
      (and
        ($FVF.lookup_Ref__Boolean_value fvf@337 ($Seq.index $t@294 k@336))
        ($FVF.lookup_Ref__Boolean_value fvf@339 ($Seq.index $t@285 k@336)))))
  :pattern (($Seq.index $t@294 k@336))
  :pattern (($Seq.index $t@294 k@336))
  :pattern (($Seq.index $t@285 k@336))))))
(check-sat)
; unsat
(pop) ; 6
; 0.03s
; (get-info :all-statistics)
(assert (forall ((k@336 Int)) (!
  (implies
    (and (<= 0 k@336) (< k@336 (+ j@272 1)))
    (=
      ($FVF.lookup_Ref__Boolean_value fvf@337 ($Seq.index $t@294 k@336))
      (and
        ($FVF.lookup_Ref__Boolean_value fvf@337 ($Seq.index $t@294 k@336))
        ($FVF.lookup_Ref__Boolean_value fvf@339 ($Seq.index $t@285 k@336)))))
  :pattern (($Seq.index $t@294 k@336))
  :pattern (($Seq.index $t@294 k@336))
  :pattern (($Seq.index $t@285 k@336)))))
(pop) ; 5
(push) ; 5
; Establish loop invariant
(declare-const $k@340 $Perm)
(assert ($Perm.isValidVar $k@340))
(assert ($Perm.isReadVar $k@340 $Perm.Write))
(set-option :timeout 0)
(push) ; 6
(assert (not (or (= $k@340 $Perm.No) true)))
(check-sat)
; unsat
(pop) ; 6
; 0.00s
; (get-info :all-statistics)
(assert (< $k@340 $k@115))
; [eval] diz.Set__max > 0
(declare-const $k@341 $Perm)
(assert ($Perm.isValidVar $k@341))
(assert ($Perm.isReadVar $k@341 $Perm.Write))
(set-option :timeout 0)
(push) ; 6
(assert (not (or (= $k@341 $Perm.No) true)))
(check-sat)
; unsat
(pop) ; 6
; 0.00s
; (get-info :all-statistics)
(assert (< $k@341 $k@117))
; [eval] |diz.Set__contents| == diz.Set__max
; [eval] |diz.Set__contents|
(declare-const fvf@342 $FVF<Int>)
(declare-const fvf@343 $FVF<Int>)
(declare-const fvf@344 $FVF<$Seq<$Ref>>)
(declare-const fvf@345 $FVF<$Seq<$Ref>>)
(assert (= ($FVF.lookup_Set__max fvf@342 diz@101) $t@116))
(assert ($Set.equal ($FVF.domain_Set__max fvf@342) ($Set.singleton  diz@101)))
(assert (= ($FVF.lookup_Set__max fvf@343 x@102) $t@123))
(assert ($Set.equal ($FVF.domain_Set__max fvf@343) ($Set.singleton  x@102)))
(assert ($Seq.equal ($FVF.lookup_Set__contents fvf@344 diz@101) $t@118))
(assert ($Set.equal ($FVF.domain_Set__contents fvf@344) ($Set.singleton  diz@101)))
(assert ($Seq.equal ($FVF.lookup_Set__contents fvf@345 x@102) $t@125))
(assert ($Set.equal ($FVF.domain_Set__contents fvf@345) ($Set.singleton  x@102)))
(declare-const k@346 Int)
; [eval] (0 <= k) && (k < diz.Set__max)
; [eval] 0 <= k
(push) ; 6
(set-option :timeout 0)
(push) ; 7
(assert (not (not (<= 0 k@346))))
(check-sat)
; unknown
(pop) ; 7
; 0.00s
; (get-info :all-statistics)
(set-option :timeout 0)
(push) ; 7
(assert (not (<= 0 k@346)))
(check-sat)
; unknown
(pop) ; 7
; 0.00s
; (get-info :all-statistics)
(push) ; 7
; [then-branch 67] 0 <= k@346
(assert (<= 0 k@346))
; [eval] k < diz.Set__max
(set-option :timeout 0)
(push) ; 8
(assert (not (< $Perm.No (+ $k@115 (ite (= diz@101 x@102) $k@122 $Perm.No)))))
(check-sat)
; unsat
(pop) ; 8
; 0.00s
; (get-info :all-statistics)
(declare-const fvf@347 $FVF<Int>)
(assert (implies
  (< $Perm.No $k@115)
  (=
    ($FVF.lookup_Set__max fvf@347 diz@101)
    ($FVF.lookup_Set__max fvf@342 diz@101))))
(assert (implies
  (ite (= diz@101 x@102) (< $Perm.No $k@122) false)
  (=
    ($FVF.lookup_Set__max fvf@347 diz@101)
    ($FVF.lookup_Set__max fvf@343 diz@101))))
(assert ($Set.equal ($FVF.domain_Set__max fvf@347) ($Set.singleton  diz@101)))
(pop) ; 7
(push) ; 7
; [else-branch 67] !0 <= k@346
(assert (not (<= 0 k@346)))
(pop) ; 7
(pop) ; 6
(assert ($Set.equal ($FVF.domain_Set__max fvf@347) ($Set.singleton  diz@101)))
(assert (implies
  (ite (= diz@101 x@102) (< $Perm.No $k@122) false)
  (=
    ($FVF.lookup_Set__max fvf@347 diz@101)
    ($FVF.lookup_Set__max fvf@343 diz@101))))
(assert (implies
  (< $Perm.No $k@115)
  (=
    ($FVF.lookup_Set__max fvf@347 diz@101)
    ($FVF.lookup_Set__max fvf@342 diz@101))))
(set-option :timeout 0)
(push) ; 6
(assert (not (not (and (<= 0 k@346) (< k@346 ($FVF.lookup_Set__max fvf@347 diz@101))))))
(check-sat)
; unknown
(pop) ; 6
; 0.00s
; (get-info :all-statistics)
(assert (and (<= 0 k@346) (< k@346 ($FVF.lookup_Set__max fvf@347 diz@101))))
; [eval] diz.Set__contents[k]
(set-option :timeout 0)
(push) ; 6
(assert (not (< $Perm.No (+ $k@117 (ite (= diz@101 x@102) $k@124 $Perm.No)))))
(check-sat)
; unsat
(pop) ; 6
; 0.00s
; (get-info :all-statistics)
(declare-const fvf@348 $FVF<$Seq<$Ref>>)
(assert (implies
  (< $Perm.No $k@117)
  ($Seq.equal
    ($FVF.lookup_Set__contents fvf@348 diz@101)
    ($FVF.lookup_Set__contents fvf@344 diz@101))))
(assert (implies
  (ite (= diz@101 x@102) (< $Perm.No $k@124) false)
  ($Seq.equal
    ($FVF.lookup_Set__contents fvf@348 diz@101)
    ($FVF.lookup_Set__contents fvf@345 diz@101))))
(assert ($Set.equal ($FVF.domain_Set__contents fvf@348) ($Set.singleton  diz@101)))
(set-option :timeout 0)
(push) ; 6
(assert (not (forall (($x Int) ($y Int)) (!
  (implies
    (and
      (and (<= 0 $x) (< $x ($FVF.lookup_Set__max fvf@347 diz@101)))
      (and (<= 0 $y) (< $y ($FVF.lookup_Set__max fvf@347 diz@101)))
      (=
        ($Seq.index ($FVF.lookup_Set__contents fvf@348 diz@101) $x)
        ($Seq.index ($FVF.lookup_Set__contents fvf@348 diz@101) $y)))
    (= $x $y))
  :pattern (($Seq.index ($FVF.lookup_Set__contents fvf@348 diz@101) $x) ($Seq.index
    ($FVF.lookup_Set__contents fvf@348 diz@101)
    $y))))))
(check-sat)
; unsat
(pop) ; 6
; 0.00s
; (get-info :all-statistics)
(declare-fun invOf@349 ($Ref) Int)
(assert (forall (($r $Ref)) (!
  (implies
    (and
      (<= 0 (invOf@349 $r))
      (< (invOf@349 $r) ($FVF.lookup_Set__max fvf@347 diz@101)))
    (=
      ($Seq.index ($FVF.lookup_Set__contents fvf@348 diz@101) (invOf@349 $r))
      $r))
  :pattern ((invOf@349 $r)))))
(assert (forall ((k@346 Int)) (!
  (implies
    (and (<= 0 k@346) (< k@346 ($FVF.lookup_Set__max fvf@347 diz@101)))
    (=
      (invOf@349 ($Seq.index ($FVF.lookup_Set__contents fvf@348 diz@101) k@346))
      k@346))
  :pattern (($Seq.index ($FVF.lookup_Set__contents fvf@348 diz@101) k@346)))))
(declare-const fvf@350 $FVF<Bool>)
; Precomputing split data for Lookup(Set__contents,fvf@348,diz@101)[k@346].Ref__Boolean_value # W
(define-fun $permsTaken31 (($r $Ref)) $Perm
  ($Perm.min
    (ite
      (and
        (<= 0 (invOf@349 $r))
        (< (invOf@349 $r) ($FVF.lookup_Set__max fvf@347 diz@101)))
      $Perm.Write
      $Perm.No)
    (ite
      (= $r ($Seq.index ($FVF.lookup_Set__contents fvf@348 diz@101) k@346))
      (ite (and (<= 0 (invOf@129 $r)) (< (invOf@129 $r) $t@123)) $k@127 $Perm.No)
      $Perm.No)))
(define-fun $permsTaken32 (($r $Ref)) $Perm
  ($Perm.min
    (-
      (ite
        (and
          (<= 0 (invOf@349 $r))
          (< (invOf@349 $r) ($FVF.lookup_Set__max fvf@347 diz@101)))
        $Perm.Write
        $Perm.No)
      ($permsTaken31 $r))
    (ite
      (= $r ($Seq.index ($FVF.lookup_Set__contents fvf@348 diz@101) k@346))
      (ite
        (and (<= 0 (invOf@121 $r)) (< (invOf@121 $r) $t@116))
        $Perm.Write
        $Perm.No)
      $Perm.No)))
; Done precomputing, updating quantified heap chunks
; Chunk depleted?
(set-option :timeout 500)
(push) ; 6
(assert (not (forall (($r $Ref)) (!
  (=
    (-
      (ite (and (<= 0 (invOf@129 $r)) (< (invOf@129 $r) $t@123)) $k@127 $Perm.No)
      ($permsTaken31 $r))
    $Perm.No)
  ))))
(check-sat)
; unknown
(pop) ; 6
; 0.00s
; (get-info :all-statistics)
; Enough permissions taken?
(set-option :timeout 500)
(push) ; 6
(assert (not (=
  (-
    (ite
      (and
        (<=
          0
          (invOf@349 ($Seq.index
            ($FVF.lookup_Set__contents fvf@348 diz@101)
            k@346)))
        (<
          (invOf@349 ($Seq.index
            ($FVF.lookup_Set__contents fvf@348 diz@101)
            k@346))
          ($FVF.lookup_Set__max fvf@347 diz@101)))
      $Perm.Write
      $Perm.No)
    ($permsTaken31 ($Seq.index ($FVF.lookup_Set__contents fvf@348 diz@101) k@346)))
  $Perm.No)))
(check-sat)
; unknown
(pop) ; 6
; 0.00s
; (get-info :all-statistics)
; Chunk depleted?
(set-option :timeout 500)
(push) ; 6
(assert (not (forall (($r $Ref)) (!
  (=
    (-
      (ite
        (and (<= 0 (invOf@121 $r)) (< (invOf@121 $r) $t@116))
        $Perm.Write
        $Perm.No)
      ($permsTaken32 $r))
    $Perm.No)
  ))))
(check-sat)
; unknown
(pop) ; 6
; 0.00s
; (get-info :all-statistics)
; Enough permissions taken?
(set-option :timeout 500)
(push) ; 6
(assert (not (=
  (-
    (-
      (ite
        (and
          (<=
            0
            (invOf@349 ($Seq.index
              ($FVF.lookup_Set__contents fvf@348 diz@101)
              k@346)))
          (<
            (invOf@349 ($Seq.index
              ($FVF.lookup_Set__contents fvf@348 diz@101)
              k@346))
            ($FVF.lookup_Set__max fvf@347 diz@101)))
        $Perm.Write
        $Perm.No)
      ($permsTaken31 ($Seq.index
        ($FVF.lookup_Set__contents fvf@348 diz@101)
        k@346)))
    ($permsTaken32 ($Seq.index ($FVF.lookup_Set__contents fvf@348 diz@101) k@346)))
  $Perm.No)))
(check-sat)
; unsat
(pop) ; 6
; 0.00s
; (get-info :all-statistics)
; Final check that enough permissions have been taken
; Done splitting
(assert (forall (($r $Ref)) (!
  (implies
    (and
      (and (<= 0 (invOf@121 $r)) (< (invOf@121 $r) $t@116))
      ($Set.in $r ($FVF.domain_Ref__Boolean_value fvf@350)))
    (=
      ($FVF.lookup_Ref__Boolean_value fvf@350 $r)
      ($FVF.lookup_Ref__Boolean_value $t@120 $r)))
  :pattern (($FVF.lookup_Ref__Boolean_value fvf@350 $r) (invOf@121 $r))
  :pattern (($FVF.lookup_Ref__Boolean_value $t@120 $r) (invOf@121 $r)))))
(assert (forall (($r $Ref)) (!
  (implies
    (and
      (ite
        (and (<= 0 (invOf@129 $r)) (< (invOf@129 $r) $t@123))
        (< $Perm.No $k@127)
        false)
      ($Set.in $r ($FVF.domain_Ref__Boolean_value fvf@350)))
    (=
      ($FVF.lookup_Ref__Boolean_value fvf@350 $r)
      ($FVF.lookup_Ref__Boolean_value $t@128 $r)))
  :pattern (($FVF.lookup_Ref__Boolean_value fvf@350 $r) (invOf@129 $r))
  :pattern (($FVF.lookup_Ref__Boolean_value $t@128 $r) (invOf@129 $r)))))
(assert (forall (($r $Ref)) (!
  (iff
    ($Set.in $r ($FVF.domain_Ref__Boolean_value fvf@350))
    (and
      (<= 0 (invOf@349 $r))
      (< (invOf@349 $r) ($FVF.lookup_Set__max fvf@347 diz@101))))
  :pattern (($Set.in $r ($FVF.domain_Ref__Boolean_value fvf@350))))))
; [eval] x != null
(declare-const $k@351 $Perm)
(assert ($Perm.isValidVar $k@351))
(assert ($Perm.isReadVar $k@351 $Perm.Write))
(set-option :timeout 0)
(push) ; 6
(assert (not (or (= $k@351 $Perm.No) true)))
(check-sat)
; unsat
(pop) ; 6
; 0.00s
; (get-info :all-statistics)
(assert (< $k@351 $k@122))
; [eval] x.Set__max > 0
(declare-const $k@352 $Perm)
(assert ($Perm.isValidVar $k@352))
(assert ($Perm.isReadVar $k@352 $Perm.Write))
(set-option :timeout 0)
(push) ; 6
(assert (not (or (= $k@352 $Perm.No) true)))
(check-sat)
; unsat
(pop) ; 6
; 0.00s
; (get-info :all-statistics)
(assert (< $k@352 $k@124))
; [eval] diz.Set__max > x.Set__max
(set-option :timeout 0)
(push) ; 6
(assert (not (> $t@116 $t@123)))
(check-sat)
; unsat
(pop) ; 6
; 0.00s
; (get-info :all-statistics)
(assert (> $t@116 $t@123))
; [eval] (j >= 0) && (j <= x.Set__max)
; [eval] j >= 0
(push) ; 6
(set-option :timeout 0)
(push) ; 7
(assert (not false))
(check-sat)
; unknown
(pop) ; 7
; 0.00s
; (get-info :all-statistics)
(push) ; 7
; [then-branch 68] True
; [eval] j <= x.Set__max
(pop) ; 7
; [dead else-branch 68] False
(pop) ; 6
(set-option :timeout 0)
(push) ; 6
(assert (not (<= 0 $t@123)))
(check-sat)
; unsat
(pop) ; 6
; 0.00s
; (get-info :all-statistics)
(assert (<= 0 $t@123))
(declare-const fvf@353 $FVF<Int>)
(declare-const fvf@354 $FVF<Int>)
(declare-const fvf@355 $FVF<$Seq<$Ref>>)
(declare-const fvf@356 $FVF<$Seq<$Ref>>)
(assert (= ($FVF.lookup_Set__max fvf@353 diz@101) $t@116))
(assert ($Set.equal ($FVF.domain_Set__max fvf@353) ($Set.singleton  diz@101)))
(assert (= ($FVF.lookup_Set__max fvf@354 x@102) $t@123))
(assert ($Set.equal ($FVF.domain_Set__max fvf@354) ($Set.singleton  x@102)))
(assert ($Seq.equal ($FVF.lookup_Set__contents fvf@355 diz@101) $t@118))
(assert ($Set.equal ($FVF.domain_Set__contents fvf@355) ($Set.singleton  diz@101)))
(assert ($Seq.equal ($FVF.lookup_Set__contents fvf@356 x@102) $t@125))
(assert ($Set.equal ($FVF.domain_Set__contents fvf@356) ($Set.singleton  x@102)))
(declare-const k@357 Int)
; [eval] (0 <= k) && (k < x.Set__max)
; [eval] 0 <= k
(push) ; 6
(set-option :timeout 0)
(push) ; 7
(assert (not (not (<= 0 k@357))))
(check-sat)
; unknown
(pop) ; 7
; 0.00s
; (get-info :all-statistics)
(set-option :timeout 0)
(push) ; 7
(assert (not (<= 0 k@357)))
(check-sat)
; unknown
(pop) ; 7
; 0.00s
; (get-info :all-statistics)
(push) ; 7
; [then-branch 69] 0 <= k@357
(assert (<= 0 k@357))
; [eval] k < x.Set__max
(set-option :timeout 0)
(push) ; 8
(assert (not (< $Perm.No (+ (ite (= x@102 diz@101) $k@115 $Perm.No) $k@122))))
(check-sat)
; unsat
(pop) ; 8
; 0.00s
; (get-info :all-statistics)
(declare-const fvf@358 $FVF<Int>)
(assert (implies
  (ite (= x@102 diz@101) (< $Perm.No $k@115) false)
  (= ($FVF.lookup_Set__max fvf@358 x@102) ($FVF.lookup_Set__max fvf@353 x@102))))
(assert (implies
  (< $Perm.No $k@122)
  (= ($FVF.lookup_Set__max fvf@358 x@102) ($FVF.lookup_Set__max fvf@354 x@102))))
(assert ($Set.equal ($FVF.domain_Set__max fvf@358) ($Set.singleton  x@102)))
(pop) ; 7
(push) ; 7
; [else-branch 69] !0 <= k@357
(assert (not (<= 0 k@357)))
(pop) ; 7
(pop) ; 6
(assert ($Set.equal ($FVF.domain_Set__max fvf@358) ($Set.singleton  x@102)))
(assert (implies
  (< $Perm.No $k@122)
  (= ($FVF.lookup_Set__max fvf@358 x@102) ($FVF.lookup_Set__max fvf@354 x@102))))
(assert (implies
  (ite (= x@102 diz@101) (< $Perm.No $k@115) false)
  (= ($FVF.lookup_Set__max fvf@358 x@102) ($FVF.lookup_Set__max fvf@353 x@102))))
(set-option :timeout 0)
(push) ; 6
(assert (not (not (and (<= 0 k@357) (< k@357 ($FVF.lookup_Set__max fvf@358 x@102))))))
(check-sat)
; unknown
(pop) ; 6
; 0.00s
; (get-info :all-statistics)
(assert (and (<= 0 k@357) (< k@357 ($FVF.lookup_Set__max fvf@358 x@102))))
(declare-const $k@359 $Perm)
(assert ($Perm.isValidVar $k@359))
(assert ($Perm.isReadVar $k@359 $Perm.Write))
(set-option :timeout 0)
(push) ; 6
(assert (not (or (= $k@359 $Perm.No) true)))
(check-sat)
; unsat
(pop) ; 6
; 0.00s
; (get-info :all-statistics)
; [eval] x.Set__contents[k]
(set-option :timeout 0)
(push) ; 6
(assert (not (< $Perm.No (+ (ite (= x@102 diz@101) $k@117 $Perm.No) $k@124))))
(check-sat)
; unsat
(pop) ; 6
; 0.00s
; (get-info :all-statistics)
(declare-const fvf@360 $FVF<$Seq<$Ref>>)
(assert (implies
  (ite (= x@102 diz@101) (< $Perm.No $k@117) false)
  ($Seq.equal
    ($FVF.lookup_Set__contents fvf@360 x@102)
    ($FVF.lookup_Set__contents fvf@355 x@102))))
(assert (implies
  (< $Perm.No $k@124)
  ($Seq.equal
    ($FVF.lookup_Set__contents fvf@360 x@102)
    ($FVF.lookup_Set__contents fvf@356 x@102))))
(assert ($Set.equal ($FVF.domain_Set__contents fvf@360) ($Set.singleton  x@102)))
(set-option :timeout 0)
(push) ; 6
(assert (not (forall (($x Int) ($y Int)) (!
  (implies
    (and
      (and (<= 0 $x) (< $x ($FVF.lookup_Set__max fvf@358 x@102)))
      (and (<= 0 $y) (< $y ($FVF.lookup_Set__max fvf@358 x@102)))
      (=
        ($Seq.index ($FVF.lookup_Set__contents fvf@360 x@102) $x)
        ($Seq.index ($FVF.lookup_Set__contents fvf@360 x@102) $y)))
    (= $x $y))
  :pattern (($Seq.index ($FVF.lookup_Set__contents fvf@360 x@102) $x) ($Seq.index
    ($FVF.lookup_Set__contents fvf@360 x@102)
    $y))))))
(check-sat)
; unsat
(pop) ; 6
; 0.00s
; (get-info :all-statistics)
(declare-fun invOf@361 ($Ref) Int)
(assert (forall (($r $Ref)) (!
  (implies
    (and
      (<= 0 (invOf@361 $r))
      (< (invOf@361 $r) ($FVF.lookup_Set__max fvf@358 x@102)))
    (= ($Seq.index ($FVF.lookup_Set__contents fvf@360 x@102) (invOf@361 $r)) $r))
  :pattern ((invOf@361 $r)))))
(assert (forall ((k@357 Int)) (!
  (implies
    (and (<= 0 k@357) (< k@357 ($FVF.lookup_Set__max fvf@358 x@102)))
    (=
      (invOf@361 ($Seq.index ($FVF.lookup_Set__contents fvf@360 x@102) k@357))
      k@357))
  :pattern (($Seq.index ($FVF.lookup_Set__contents fvf@360 x@102) k@357)))))
(declare-const fvf@362 $FVF<Bool>)
; Precomputing split data for Lookup(Set__contents,fvf@360,x@102)[k@357].Ref__Boolean_value # $k@359
(define-fun $permsTaken33 (($r $Ref)) $Perm
  ($Perm.min
    (ite
      (and
        (<= 0 (invOf@361 $r))
        (< (invOf@361 $r) ($FVF.lookup_Set__max fvf@358 x@102)))
      $k@359
      $Perm.No)
    (ite
      (= $r ($Seq.index ($FVF.lookup_Set__contents fvf@360 x@102) k@357))
      (-
        (ite
          (and (<= 0 (invOf@129 $r)) (< (invOf@129 $r) $t@123))
          $k@127
          $Perm.No)
        ($permsTaken31 $r))
      $Perm.No)))
(define-fun $permsTaken34 (($r $Ref)) $Perm
  ($Perm.min
    (-
      (ite
        (and
          (<= 0 (invOf@361 $r))
          (< (invOf@361 $r) ($FVF.lookup_Set__max fvf@358 x@102)))
        $k@359
        $Perm.No)
      ($permsTaken33 $r))
    (ite
      (= $r ($Seq.index ($FVF.lookup_Set__contents fvf@360 x@102) k@357))
      (-
        (ite
          (and (<= 0 (invOf@121 $r)) (< (invOf@121 $r) $t@116))
          $Perm.Write
          $Perm.No)
        ($permsTaken32 $r))
      $Perm.No)))
; Done precomputing, updating quantified heap chunks
; Constrain original permissions $k@359
(assert (forall (($r $Ref)) (!
  (implies
    (not
      (=
        (-
          (ite
            (and (<= 0 (invOf@129 $r)) (< (invOf@129 $r) $t@123))
            $k@127
            $Perm.No)
          ($permsTaken31 $r))
        $Perm.No))
    (<
      (ite
        (and
          (<= 0 (invOf@361 $r))
          (< (invOf@361 $r) ($FVF.lookup_Set__max fvf@358 x@102)))
        $k@359
        $Perm.No)
      (-
        (ite
          (and (<= 0 (invOf@129 $r)) (< (invOf@129 $r) $t@123))
          $k@127
          $Perm.No)
        ($permsTaken31 $r))))
  :pattern ((invOf@129 $r))
  :pattern ((invOf@129 $r))
  :pattern ((invOf@361 $r))
  :pattern ((invOf@361 $r))
  :pattern ((invOf@129 $r))
  :pattern ((invOf@129 $r)))))
; Enough permissions taken?
(set-option :timeout 500)
(push) ; 6
(assert (not (=
  (-
    (ite
      (and
        (<=
          0
          (invOf@361 ($Seq.index ($FVF.lookup_Set__contents fvf@360 x@102) k@357)))
        (<
          (invOf@361 ($Seq.index ($FVF.lookup_Set__contents fvf@360 x@102) k@357))
          ($FVF.lookup_Set__max fvf@358 x@102)))
      $k@359
      $Perm.No)
    ($permsTaken33 ($Seq.index ($FVF.lookup_Set__contents fvf@360 x@102) k@357)))
  $Perm.No)))
(check-sat)
; unknown
(pop) ; 6
; 0.00s
; (get-info :all-statistics)
; Constrain original permissions $k@359
(assert (forall (($r $Ref)) (!
  (implies
    (not
      (=
        (-
          (ite
            (and (<= 0 (invOf@121 $r)) (< (invOf@121 $r) $t@116))
            $Perm.Write
            $Perm.No)
          ($permsTaken32 $r))
        $Perm.No))
    (<
      (ite
        (and
          (<= 0 (invOf@361 $r))
          (< (invOf@361 $r) ($FVF.lookup_Set__max fvf@358 x@102)))
        $k@359
        $Perm.No)
      (-
        (ite
          (and (<= 0 (invOf@121 $r)) (< (invOf@121 $r) $t@116))
          $Perm.Write
          $Perm.No)
        ($permsTaken32 $r))))
  :pattern ((invOf@121 $r))
  :pattern ((invOf@121 $r))
  :pattern ((invOf@361 $r))
  :pattern ((invOf@361 $r))
  :pattern ((invOf@121 $r))
  :pattern ((invOf@121 $r)))))
; Enough permissions taken?
(set-option :timeout 500)
(push) ; 6
(assert (not (=
  (-
    (-
      (ite
        (and
          (<=
            0
            (invOf@361 ($Seq.index
              ($FVF.lookup_Set__contents fvf@360 x@102)
              k@357)))
          (<
            (invOf@361 ($Seq.index
              ($FVF.lookup_Set__contents fvf@360 x@102)
              k@357))
            ($FVF.lookup_Set__max fvf@358 x@102)))
        $k@359
        $Perm.No)
      ($permsTaken33 ($Seq.index ($FVF.lookup_Set__contents fvf@360 x@102) k@357)))
    ($permsTaken34 ($Seq.index ($FVF.lookup_Set__contents fvf@360 x@102) k@357)))
  $Perm.No)))
(check-sat)
; unsat
(pop) ; 6
; 0.01s
; (get-info :all-statistics)
; Final check that enough permissions have been taken
; Done splitting
(assert (forall (($r $Ref)) (!
  (implies
    (and
      (<
        $Perm.No
        (-
          (ite
            (and (<= 0 (invOf@121 $r)) (< (invOf@121 $r) $t@116))
            $Perm.Write
            $Perm.No)
          ($permsTaken32 $r)))
      ($Set.in $r ($FVF.domain_Ref__Boolean_value fvf@362)))
    (=
      ($FVF.lookup_Ref__Boolean_value fvf@362 $r)
      ($FVF.lookup_Ref__Boolean_value $t@120 $r)))
  :pattern (($FVF.lookup_Ref__Boolean_value fvf@362 $r) (invOf@121 $r))
  :pattern (($FVF.lookup_Ref__Boolean_value $t@120 $r) (invOf@121 $r)))))
(assert (forall (($r $Ref)) (!
  (implies
    (and
      (<
        $Perm.No
        (-
          (ite
            (and (<= 0 (invOf@129 $r)) (< (invOf@129 $r) $t@123))
            $k@127
            $Perm.No)
          ($permsTaken31 $r)))
      ($Set.in $r ($FVF.domain_Ref__Boolean_value fvf@362)))
    (=
      ($FVF.lookup_Ref__Boolean_value fvf@362 $r)
      ($FVF.lookup_Ref__Boolean_value $t@128 $r)))
  :pattern (($FVF.lookup_Ref__Boolean_value fvf@362 $r) (invOf@129 $r))
  :pattern (($FVF.lookup_Ref__Boolean_value $t@128 $r) (invOf@129 $r)))))
(assert (forall (($r $Ref)) (!
  (iff
    ($Set.in $r ($FVF.domain_Ref__Boolean_value fvf@362))
    (and
      (<= 0 (invOf@361 $r))
      (< (invOf@361 $r) ($FVF.lookup_Set__max fvf@358 x@102))))
  :pattern (($Set.in $r ($FVF.domain_Ref__Boolean_value fvf@362))))))
; [eval] (forall k: Int :: (0 <= k) && (k < j) ==> (diz.Set__contents[k].Ref__Boolean_value == diz.Set__contents[k].Ref__Boolean_value && x.Set__contents[k].Ref__Boolean_value))
(declare-const k@363 Int)
(push) ; 6
; [eval] (0 <= k) && (k < j) ==> (diz.Set__contents[k].Ref__Boolean_value == diz.Set__contents[k].Ref__Boolean_value && x.Set__contents[k].Ref__Boolean_value)
; [eval] (0 <= k) && (k < j)
; [eval] 0 <= k
(push) ; 7
(set-option :timeout 0)
(push) ; 8
(assert (not (not (<= 0 k@363))))
(check-sat)
; unknown
(pop) ; 8
; 0.00s
; (get-info :all-statistics)
(set-option :timeout 0)
(push) ; 8
(assert (not (<= 0 k@363)))
(check-sat)
; unknown
(pop) ; 8
; 0.00s
; (get-info :all-statistics)
(push) ; 8
; [then-branch 70] 0 <= k@363
(assert (<= 0 k@363))
; [eval] k < j
(pop) ; 8
(push) ; 8
; [else-branch 70] !0 <= k@363
(assert (not (<= 0 k@363)))
(pop) ; 8
(pop) ; 7
(push) ; 7
(set-option :timeout 0)
(push) ; 8
(assert (not (not (and (<= 0 k@363) (< k@363 0)))))
(check-sat)
; unsat
(pop) ; 8
; 0.00s
; (get-info :all-statistics)
(set-option :timeout 0)
(push) ; 8
(assert (not (and (<= 0 k@363) (< k@363 0))))
(check-sat)
; unknown
(pop) ; 8
; 0.00s
; (get-info :all-statistics)
; [dead then-branch 71] 0 <= k@363 && k@363 < 0
(push) ; 8
; [else-branch 71] !0 <= k@363 && k@363 < 0
(assert (not (and (<= 0 k@363) (< k@363 0))))
(pop) ; 8
(pop) ; 7
(pop) ; 6
(set-option :timeout 0)
(push) ; 6
(assert (not (forall ((k@363 Int)) (!
  true
  :pattern ()
  :pattern ()
  :pattern ()))))
(check-sat)
; unsat
(pop) ; 6
; 0.00s
; (get-info :all-statistics)
(assert (forall ((k@363 Int)) (!
  true
  :pattern ()
  :pattern ()
  :pattern ())))
; Continue after loop
(declare-const $t@364 $Snap)
(declare-const $t@365 $Snap)
(assert (= $t@364 ($Snap.combine $t@365 $Snap.unit)))
(declare-const $t@366 $Snap)
(assert (= $t@365 ($Snap.combine $t@366 $Snap.unit)))
(declare-const $t@367 $Snap)
(declare-const $t@368 $FVF<Bool>)
(assert (= $t@366 ($Snap.combine $t@367 ($SortWrappers.$FVF<Bool>To$Snap $t@368))))
(declare-const $t@369 $Snap)
(assert (= $t@367 ($Snap.combine $t@369 $Snap.unit)))
(declare-const $t@370 $Snap)
(assert (= $t@369 ($Snap.combine $t@370 $Snap.unit)))
(declare-const $t@371 $Snap)
(declare-const $t@372 $Seq<$Ref>)
(assert (= $t@370 ($Snap.combine $t@371 ($SortWrappers.$Seq<$Ref>To$Snap $t@372))))
(declare-const $t@373 $Snap)
(assert (= $t@371 ($Snap.combine $t@373 $Snap.unit)))
(declare-const $t@374 $Snap)
(declare-const $t@375 Int)
(assert (= $t@373 ($Snap.combine $t@374 ($SortWrappers.IntTo$Snap $t@375))))
(declare-const $t@376 $Snap)
(assert (= $t@374 ($Snap.combine $t@376 $Snap.unit)))
(declare-const $t@377 $Snap)
(declare-const $t@378 $FVF<Bool>)
(assert (= $t@376 ($Snap.combine $t@377 ($SortWrappers.$FVF<Bool>To$Snap $t@378))))
(declare-const $t@379 $Snap)
(assert (= $t@377 ($Snap.combine $t@379 $Snap.unit)))
(declare-const $t@380 Int)
(declare-const $t@381 $Seq<$Ref>)
(assert (=
  $t@379
  ($Snap.combine
    ($SortWrappers.IntTo$Snap $t@380)
    ($SortWrappers.$Seq<$Ref>To$Snap $t@381))))
(declare-const $t@382 Int)
(assert (=
  ($SortWrappers.IntTo$Snap $t@380)
  ($Snap.combine ($SortWrappers.IntTo$Snap $t@382) $Snap.unit)))
(declare-const $k@383 $Perm)
(assert ($Perm.isValidVar $k@383))
(assert ($Perm.isReadVar $k@383 $Perm.Write))
(assert (implies (< $Perm.No (- $k@115 $k@340)) (= $t@382 $t@116)))
; [eval] diz.Set__max > 0
(set-option :timeout 0)
(push) ; 6
(assert (not (not (= (+ (- $k@115 $k@340) $k@383) $Perm.No))))
(check-sat)
; unsat
(pop) ; 6
; 0.00s
; (get-info :all-statistics)
(assert (not (= (+ (- $k@115 $k@340) $k@383) $Perm.No)))
(assert (> $t@382 0))
(declare-const $k@384 $Perm)
(assert ($Perm.isValidVar $k@384))
(assert ($Perm.isReadVar $k@384 $Perm.Write))
(assert (implies (< $Perm.No (- $k@117 $k@341)) ($Seq.equal $t@381 $t@118)))
; [eval] |diz.Set__contents| == diz.Set__max
; [eval] |diz.Set__contents|
(set-option :timeout 0)
(push) ; 6
(assert (not (not (= (+ (- $k@117 $k@341) $k@384) $Perm.No))))
(check-sat)
; unsat
(pop) ; 6
; 0.00s
; (get-info :all-statistics)
(assert (not (= (+ (- $k@117 $k@341) $k@384) $Perm.No)))
(assert (= ($Seq.length $t@381) $t@382))
(declare-const k@385 Int)
(push) ; 6
; [eval] (0 <= k) && (k < diz.Set__max)
; [eval] 0 <= k
(push) ; 7
(set-option :timeout 0)
(push) ; 8
(assert (not (not (<= 0 k@385))))
(check-sat)
; unknown
(pop) ; 8
; 0.00s
; (get-info :all-statistics)
(set-option :timeout 0)
(push) ; 8
(assert (not (<= 0 k@385)))
(check-sat)
; unknown
(pop) ; 8
; 0.00s
; (get-info :all-statistics)
(push) ; 8
; [then-branch 72] 0 <= k@385
(assert (<= 0 k@385))
; [eval] k < diz.Set__max
(pop) ; 8
(push) ; 8
; [else-branch 72] !0 <= k@385
(assert (not (<= 0 k@385)))
(pop) ; 8
(pop) ; 7
(assert (and (<= 0 k@385) (< k@385 $t@382)))
; [eval] diz.Set__contents[k]
(pop) ; 6
(declare-fun invOf@386 ($Ref) Int)
(assert (forall (($r $Ref)) (!
  (implies
    (and (<= 0 (invOf@386 $r)) (< (invOf@386 $r) $t@382))
    (= ($Seq.index $t@381 (invOf@386 $r)) $r))
  :pattern ((invOf@386 $r)))))
(assert (forall ((k@385 Int)) (!
  (implies
    (and (<= 0 k@385) (< k@385 $t@382))
    (= (invOf@386 ($Seq.index $t@381 k@385)) k@385))
  :pattern (($Seq.index $t@381 k@385)))))
(assert (forall ((k@385 Int)) (!
  (iff
    ($Set.in ($Seq.index $t@381 k@385) ($FVF.domain_Ref__Boolean_value $t@378))
    (and (<= 0 k@385) (< k@385 $t@382)))
  :pattern (($Set.in
    ($Seq.index $t@381 k@385)
    ($FVF.domain_Ref__Boolean_value $t@378))))))
(assert (forall ((k@385 Int)) (!
  (implies
    (and (<= 0 k@385) (< k@385 $t@382))
    (not (= ($Seq.index $t@381 k@385) $Ref.null)))
  :pattern (($Seq.index $t@381 k@385)))))
; [eval] x != null
(declare-const $k@387 $Perm)
(assert ($Perm.isValidVar $k@387))
(assert ($Perm.isReadVar $k@387 $Perm.Write))
(assert (implies (< $Perm.No (- $k@122 $k@351)) (= $t@375 $t@123)))
; [eval] x.Set__max > 0
(set-option :timeout 0)
(push) ; 6
(assert (not (not (= (+ (- $k@122 $k@351) $k@387) $Perm.No))))
(check-sat)
; unsat
(pop) ; 6
; 0.00s
; (get-info :all-statistics)
(assert (not (= (+ (- $k@122 $k@351) $k@387) $Perm.No)))
(assert (> $t@375 0))
(declare-const $k@388 $Perm)
(assert ($Perm.isValidVar $k@388))
(assert ($Perm.isReadVar $k@388 $Perm.Write))
(assert (implies (< $Perm.No (- $k@124 $k@352)) ($Seq.equal $t@372 $t@125)))
; [eval] diz.Set__max > x.Set__max
(assert (> $t@382 $t@375))
; [eval] (j >= 0) && (j <= x.Set__max)
; [eval] j >= 0
(push) ; 6
(set-option :timeout 0)
(push) ; 7
(assert (not (not (>= j@272 0))))
(check-sat)
; unknown
(pop) ; 7
; 0.00s
; (get-info :all-statistics)
(set-option :timeout 0)
(push) ; 7
(assert (not (>= j@272 0)))
(check-sat)
; unknown
(pop) ; 7
; 0.00s
; (get-info :all-statistics)
(push) ; 7
; [then-branch 73] j@272 >= 0
(assert (>= j@272 0))
; [eval] j <= x.Set__max
(pop) ; 7
(push) ; 7
; [else-branch 73] !j@272 >= 0
(assert (not (>= j@272 0)))
(pop) ; 7
(pop) ; 6
(assert (and (>= j@272 0) (<= j@272 $t@375)))
(declare-const k@389 Int)
(push) ; 6
; [eval] (0 <= k) && (k < x.Set__max)
; [eval] 0 <= k
(push) ; 7
(set-option :timeout 0)
(push) ; 8
(assert (not (not (<= 0 k@389))))
(check-sat)
; unknown
(pop) ; 8
; 0.00s
; (get-info :all-statistics)
(set-option :timeout 0)
(push) ; 8
(assert (not (<= 0 k@389)))
(check-sat)
; unknown
(pop) ; 8
; 0.00s
; (get-info :all-statistics)
(push) ; 8
; [then-branch 74] 0 <= k@389
(assert (<= 0 k@389))
; [eval] k < x.Set__max
(pop) ; 8
(push) ; 8
; [else-branch 74] !0 <= k@389
(assert (not (<= 0 k@389)))
(pop) ; 8
(pop) ; 7
(assert (and (<= 0 k@389) (< k@389 $t@375)))
; [eval] x.Set__contents[k]
(set-option :timeout 0)
(push) ; 7
(assert (not (not (= (+ (- $k@124 $k@352) $k@388) $Perm.No))))
(check-sat)
; unsat
(pop) ; 7
; 0.00s
; (get-info :all-statistics)
(assert (not (= (+ (- $k@124 $k@352) $k@388) $Perm.No)))
(declare-const $k@390 $Perm)
(assert ($Perm.isValidVar $k@390))
(assert ($Perm.isReadVar $k@390 $Perm.Write))
(pop) ; 6
(assert (not (= (+ (- $k@124 $k@352) $k@388) $Perm.No)))
(assert ($Perm.isValidVar $k@390))
(assert ($Perm.isReadVar $k@390 $Perm.Write))
(declare-fun invOf@391 ($Ref) Int)
(assert (forall (($r $Ref)) (!
  (implies
    (and (<= 0 (invOf@391 $r)) (< (invOf@391 $r) $t@375))
    (= ($Seq.index $t@372 (invOf@391 $r)) $r))
  :pattern ((invOf@391 $r)))))
(assert (forall ((k@389 Int)) (!
  (implies
    (and (<= 0 k@389) (< k@389 $t@375))
    (= (invOf@391 ($Seq.index $t@372 k@389)) k@389))
  :pattern (($Seq.index $t@372 k@389)))))
(assert (forall ((k@389 Int)) (!
  (iff
    ($Set.in ($Seq.index $t@372 k@389) ($FVF.domain_Ref__Boolean_value $t@368))
    (and (<= 0 k@389) (< k@389 $t@375)))
  :pattern (($Set.in
    ($Seq.index $t@372 k@389)
    ($FVF.domain_Ref__Boolean_value $t@368))))))
(assert (forall ((k@389 Int)) (!
  (implies
    (and (and (<= 0 k@389) (< k@389 $t@375)) (< $Perm.No $k@390))
    (not (= ($Seq.index $t@372 k@389) $Ref.null)))
  :pattern (($Seq.index $t@372 k@389)))))
(assert (< $Perm.No $k@390))
; [eval] (forall k: Int :: (0 <= k) && (k < j) ==> (diz.Set__contents[k].Ref__Boolean_value == diz.Set__contents[k].Ref__Boolean_value && x.Set__contents[k].Ref__Boolean_value))
(declare-const k@392 Int)
(push) ; 6
; [eval] (0 <= k) && (k < j) ==> (diz.Set__contents[k].Ref__Boolean_value == diz.Set__contents[k].Ref__Boolean_value && x.Set__contents[k].Ref__Boolean_value)
; [eval] (0 <= k) && (k < j)
; [eval] 0 <= k
(push) ; 7
(set-option :timeout 0)
(push) ; 8
(assert (not (not (<= 0 k@392))))
(check-sat)
; unknown
(pop) ; 8
; 0.00s
; (get-info :all-statistics)
(set-option :timeout 0)
(push) ; 8
(assert (not (<= 0 k@392)))
(check-sat)
; unknown
(pop) ; 8
; 0.00s
; (get-info :all-statistics)
(push) ; 8
; [then-branch 75] 0 <= k@392
(assert (<= 0 k@392))
; [eval] k < j
(pop) ; 8
(push) ; 8
; [else-branch 75] !0 <= k@392
(assert (not (<= 0 k@392)))
(pop) ; 8
(pop) ; 7
(push) ; 7
(set-option :timeout 0)
(push) ; 8
(assert (not (not (and (<= 0 k@392) (< k@392 j@272)))))
(check-sat)
; unknown
(pop) ; 8
; 0.00s
; (get-info :all-statistics)
(set-option :timeout 0)
(push) ; 8
(assert (not (and (<= 0 k@392) (< k@392 j@272))))
(check-sat)
; unknown
(pop) ; 8
; 0.00s
; (get-info :all-statistics)
(push) ; 8
; [then-branch 76] 0 <= k@392 && k@392 < j@272
(assert (and (<= 0 k@392) (< k@392 j@272)))
; [eval] diz.Set__contents[k].Ref__Boolean_value == diz.Set__contents[k].Ref__Boolean_value && x.Set__contents[k].Ref__Boolean_value
; [eval] diz.Set__contents[k]
(set-option :timeout 0)
(push) ; 9
(assert (not (not (= ($Seq.index $t@381 k@392) $Ref.null))))
(check-sat)
; unsat
(pop) ; 9
; 0.00s
; (get-info :all-statistics)
(set-option :timeout 0)
(push) ; 9
(assert (not (<
  $Perm.No
  (+
    (+
      (+
        (-
          (-
            (ite
              (and
                (<= 0 (invOf@121 ($Seq.index $t@381 k@392)))
                (< (invOf@121 ($Seq.index $t@381 k@392)) $t@116))
              $Perm.Write
              $Perm.No)
            ($permsTaken32 ($Seq.index $t@381 k@392)))
          ($permsTaken34 ($Seq.index $t@381 k@392)))
        (-
          (-
            (ite
              (and
                (<= 0 (invOf@129 ($Seq.index $t@381 k@392)))
                (< (invOf@129 ($Seq.index $t@381 k@392)) $t@123))
              $k@127
              $Perm.No)
            ($permsTaken31 ($Seq.index $t@381 k@392)))
          ($permsTaken33 ($Seq.index $t@381 k@392))))
      (ite
        (and
          (<= 0 (invOf@386 ($Seq.index $t@381 k@392)))
          (< (invOf@386 ($Seq.index $t@381 k@392)) $t@382))
        $Perm.Write
        $Perm.No))
    (ite
      (and
        (<= 0 (invOf@391 ($Seq.index $t@381 k@392)))
        (< (invOf@391 ($Seq.index $t@381 k@392)) $t@375))
      $k@390
      $Perm.No)))))
(check-sat)
; unsat
(pop) ; 9
; 0.04s
; (get-info :all-statistics)
(declare-const fvf@393 $FVF<Bool>)
(assert (forall (($r $Ref)) (!
  (implies
    (and
      (<
        $Perm.No
        (-
          (-
            (ite
              (and (<= 0 (invOf@121 $r)) (< (invOf@121 $r) $t@116))
              $Perm.Write
              $Perm.No)
            ($permsTaken32 $r))
          ($permsTaken34 $r)))
      ($Set.in $r ($FVF.domain_Ref__Boolean_value fvf@393)))
    (=
      ($FVF.lookup_Ref__Boolean_value fvf@393 $r)
      ($FVF.lookup_Ref__Boolean_value $t@120 $r)))
  :pattern (($FVF.lookup_Ref__Boolean_value fvf@393 $r) (invOf@121 $r))
  :pattern (($FVF.lookup_Ref__Boolean_value $t@120 $r) (invOf@121 $r)))))
(assert (forall (($r $Ref)) (!
  (implies
    (and
      (<
        $Perm.No
        (-
          (-
            (ite
              (and (<= 0 (invOf@129 $r)) (< (invOf@129 $r) $t@123))
              $k@127
              $Perm.No)
            ($permsTaken31 $r))
          ($permsTaken33 $r)))
      ($Set.in $r ($FVF.domain_Ref__Boolean_value fvf@393)))
    (=
      ($FVF.lookup_Ref__Boolean_value fvf@393 $r)
      ($FVF.lookup_Ref__Boolean_value $t@128 $r)))
  :pattern (($FVF.lookup_Ref__Boolean_value fvf@393 $r) (invOf@129 $r))
  :pattern (($FVF.lookup_Ref__Boolean_value $t@128 $r) (invOf@129 $r)))))
(assert (forall (($r $Ref)) (!
  (implies
    (and
      (and (<= 0 (invOf@386 $r)) (< (invOf@386 $r) $t@382))
      ($Set.in $r ($FVF.domain_Ref__Boolean_value fvf@393)))
    (=
      ($FVF.lookup_Ref__Boolean_value fvf@393 $r)
      ($FVF.lookup_Ref__Boolean_value $t@378 $r)))
  :pattern (($FVF.lookup_Ref__Boolean_value fvf@393 $r) (invOf@386 $r))
  :pattern (($FVF.lookup_Ref__Boolean_value $t@378 $r) (invOf@386 $r)))))
(assert (forall (($r $Ref)) (!
  (implies
    (and
      (ite
        (and (<= 0 (invOf@391 $r)) (< (invOf@391 $r) $t@375))
        (< $Perm.No $k@390)
        false)
      ($Set.in $r ($FVF.domain_Ref__Boolean_value fvf@393)))
    (=
      ($FVF.lookup_Ref__Boolean_value fvf@393 $r)
      ($FVF.lookup_Ref__Boolean_value $t@368 $r)))
  :pattern (($FVF.lookup_Ref__Boolean_value fvf@393 $r) (invOf@391 $r))
  :pattern (($FVF.lookup_Ref__Boolean_value $t@368 $r) (invOf@391 $r)))))
(assert (forall ((k@392 Int)) (!
  (iff
    ($Set.in ($Seq.index $t@381 k@392) ($FVF.domain_Ref__Boolean_value fvf@393))
    (and (and (<= 0 k@392) (< k@392 j@272)) (not (<= $t@116 $t@123))))
  :pattern (($Set.in
    ($Seq.index $t@381 k@392)
    ($FVF.domain_Ref__Boolean_value fvf@393))))))
; [eval] diz.Set__contents[k].Ref__Boolean_value && x.Set__contents[k].Ref__Boolean_value
; [eval] diz.Set__contents[k]
(set-option :timeout 0)
(push) ; 9
(assert (not (not (= ($Seq.index $t@381 k@392) $Ref.null))))
(check-sat)
; unsat
(pop) ; 9
; 0.00s
; (get-info :all-statistics)
(set-option :timeout 0)
(push) ; 9
(assert (not (<
  $Perm.No
  (+
    (+
      (+
        (-
          (-
            (ite
              (and
                (<= 0 (invOf@121 ($Seq.index $t@381 k@392)))
                (< (invOf@121 ($Seq.index $t@381 k@392)) $t@116))
              $Perm.Write
              $Perm.No)
            ($permsTaken32 ($Seq.index $t@381 k@392)))
          ($permsTaken34 ($Seq.index $t@381 k@392)))
        (-
          (-
            (ite
              (and
                (<= 0 (invOf@129 ($Seq.index $t@381 k@392)))
                (< (invOf@129 ($Seq.index $t@381 k@392)) $t@123))
              $k@127
              $Perm.No)
            ($permsTaken31 ($Seq.index $t@381 k@392)))
          ($permsTaken33 ($Seq.index $t@381 k@392))))
      (ite
        (and
          (<= 0 (invOf@386 ($Seq.index $t@381 k@392)))
          (< (invOf@386 ($Seq.index $t@381 k@392)) $t@382))
        $Perm.Write
        $Perm.No))
    (ite
      (and
        (<= 0 (invOf@391 ($Seq.index $t@381 k@392)))
        (< (invOf@391 ($Seq.index $t@381 k@392)) $t@375))
      $k@390
      $Perm.No)))))
(check-sat)
; unsat
(pop) ; 9
; 0.05s
; (get-info :all-statistics)
(declare-const fvf@394 $FVF<Bool>)
(push) ; 9
(set-option :timeout 0)
(push) ; 10
(assert (not (not ($FVF.lookup_Ref__Boolean_value fvf@393 ($Seq.index $t@381 k@392)))))
(check-sat)
; unknown
(pop) ; 10
; 0.04s
; (get-info :all-statistics)
(set-option :timeout 0)
(push) ; 10
(assert (not ($FVF.lookup_Ref__Boolean_value fvf@393 ($Seq.index $t@381 k@392))))
(check-sat)
; unknown
(pop) ; 10
; 0.05s
; (get-info :all-statistics)
(push) ; 10
; [then-branch 77] Lookup(Ref__Boolean_value,fvf@393,$t@381[k@392])
(assert ($FVF.lookup_Ref__Boolean_value fvf@393 ($Seq.index $t@381 k@392)))
; [eval] x.Set__contents[k]
(set-option :timeout 0)
(push) ; 11
(assert (not (not (= ($Seq.index $t@372 k@392) $Ref.null))))
(check-sat)
; unsat
(pop) ; 11
; 0.00s
; (get-info :all-statistics)
(set-option :timeout 0)
(push) ; 11
(assert (not (<
  $Perm.No
  (+
    (+
      (+
        (-
          (-
            (ite
              (and
                (<= 0 (invOf@121 ($Seq.index $t@372 k@392)))
                (< (invOf@121 ($Seq.index $t@372 k@392)) $t@116))
              $Perm.Write
              $Perm.No)
            ($permsTaken32 ($Seq.index $t@372 k@392)))
          ($permsTaken34 ($Seq.index $t@372 k@392)))
        (-
          (-
            (ite
              (and
                (<= 0 (invOf@129 ($Seq.index $t@372 k@392)))
                (< (invOf@129 ($Seq.index $t@372 k@392)) $t@123))
              $k@127
              $Perm.No)
            ($permsTaken31 ($Seq.index $t@372 k@392)))
          ($permsTaken33 ($Seq.index $t@372 k@392))))
      (ite
        (and
          (<= 0 (invOf@386 ($Seq.index $t@372 k@392)))
          (< (invOf@386 ($Seq.index $t@372 k@392)) $t@382))
        $Perm.Write
        $Perm.No))
    (ite
      (and
        (<= 0 (invOf@391 ($Seq.index $t@372 k@392)))
        (< (invOf@391 ($Seq.index $t@372 k@392)) $t@375))
      $k@390
      $Perm.No)))))
(check-sat)
; unsat
(pop) ; 11
; 0.04s
; (get-info :all-statistics)
(declare-const fvf@395 $FVF<Bool>)
(assert (forall (($r $Ref)) (!
  (implies
    (and
      (<
        $Perm.No
        (-
          (-
            (ite
              (and (<= 0 (invOf@121 $r)) (< (invOf@121 $r) $t@116))
              $Perm.Write
              $Perm.No)
            ($permsTaken32 $r))
          ($permsTaken34 $r)))
      ($Set.in $r ($FVF.domain_Ref__Boolean_value fvf@395)))
    (=
      ($FVF.lookup_Ref__Boolean_value fvf@395 $r)
      ($FVF.lookup_Ref__Boolean_value $t@120 $r)))
  :pattern (($FVF.lookup_Ref__Boolean_value fvf@395 $r) (invOf@121 $r))
  :pattern (($FVF.lookup_Ref__Boolean_value $t@120 $r) (invOf@121 $r)))))
(assert (forall (($r $Ref)) (!
  (implies
    (and
      (<
        $Perm.No
        (-
          (-
            (ite
              (and (<= 0 (invOf@129 $r)) (< (invOf@129 $r) $t@123))
              $k@127
              $Perm.No)
            ($permsTaken31 $r))
          ($permsTaken33 $r)))
      ($Set.in $r ($FVF.domain_Ref__Boolean_value fvf@395)))
    (=
      ($FVF.lookup_Ref__Boolean_value fvf@395 $r)
      ($FVF.lookup_Ref__Boolean_value $t@128 $r)))
  :pattern (($FVF.lookup_Ref__Boolean_value fvf@395 $r) (invOf@129 $r))
  :pattern (($FVF.lookup_Ref__Boolean_value $t@128 $r) (invOf@129 $r)))))
(assert (forall (($r $Ref)) (!
  (implies
    (and
      (and (<= 0 (invOf@386 $r)) (< (invOf@386 $r) $t@382))
      ($Set.in $r ($FVF.domain_Ref__Boolean_value fvf@395)))
    (=
      ($FVF.lookup_Ref__Boolean_value fvf@395 $r)
      ($FVF.lookup_Ref__Boolean_value $t@378 $r)))
  :pattern (($FVF.lookup_Ref__Boolean_value fvf@395 $r) (invOf@386 $r))
  :pattern (($FVF.lookup_Ref__Boolean_value $t@378 $r) (invOf@386 $r)))))
(assert (forall (($r $Ref)) (!
  (implies
    (and
      (ite
        (and (<= 0 (invOf@391 $r)) (< (invOf@391 $r) $t@375))
        (< $Perm.No $k@390)
        false)
      ($Set.in $r ($FVF.domain_Ref__Boolean_value fvf@395)))
    (=
      ($FVF.lookup_Ref__Boolean_value fvf@395 $r)
      ($FVF.lookup_Ref__Boolean_value $t@368 $r)))
  :pattern (($FVF.lookup_Ref__Boolean_value fvf@395 $r) (invOf@391 $r))
  :pattern (($FVF.lookup_Ref__Boolean_value $t@368 $r) (invOf@391 $r)))))
(assert (forall ((k@392 Int)) (!
  (iff
    ($Set.in ($Seq.index $t@372 k@392) ($FVF.domain_Ref__Boolean_value fvf@395))
    (and
      ($FVF.lookup_Ref__Boolean_value fvf@393 ($Seq.index $t@381 k@392))
      (and (<= 0 k@392) (< k@392 j@272))
      (not (<= $t@116 $t@123))))
  :pattern (($Set.in
    ($Seq.index $t@372 k@392)
    ($FVF.domain_Ref__Boolean_value fvf@395))))))
(pop) ; 10
(push) ; 10
; [else-branch 77] !Lookup(Ref__Boolean_value,fvf@393,$t@381[k@392])
(assert (not ($FVF.lookup_Ref__Boolean_value fvf@393 ($Seq.index $t@381 k@392))))
(pop) ; 10
(pop) ; 9
(assert (forall ((k@392 Int)) (!
  (iff
    ($Set.in ($Seq.index $t@372 k@392) ($FVF.domain_Ref__Boolean_value fvf@395))
    (and
      ($FVF.lookup_Ref__Boolean_value fvf@393 ($Seq.index $t@381 k@392))
      (and (<= 0 k@392) (< k@392 j@272))
      (not (<= $t@116 $t@123))))
  :pattern (($Set.in
    ($Seq.index $t@372 k@392)
    ($FVF.domain_Ref__Boolean_value fvf@395))))))
(assert (forall (($r $Ref)) (!
  (implies
    (and
      (ite
        (and (<= 0 (invOf@391 $r)) (< (invOf@391 $r) $t@375))
        (< $Perm.No $k@390)
        false)
      ($Set.in $r ($FVF.domain_Ref__Boolean_value fvf@395)))
    (=
      ($FVF.lookup_Ref__Boolean_value fvf@395 $r)
      ($FVF.lookup_Ref__Boolean_value $t@368 $r)))
  :pattern (($FVF.lookup_Ref__Boolean_value fvf@395 $r) (invOf@391 $r))
  :pattern (($FVF.lookup_Ref__Boolean_value $t@368 $r) (invOf@391 $r)))))
(assert (forall (($r $Ref)) (!
  (implies
    (and
      (and (<= 0 (invOf@386 $r)) (< (invOf@386 $r) $t@382))
      ($Set.in $r ($FVF.domain_Ref__Boolean_value fvf@395)))
    (=
      ($FVF.lookup_Ref__Boolean_value fvf@395 $r)
      ($FVF.lookup_Ref__Boolean_value $t@378 $r)))
  :pattern (($FVF.lookup_Ref__Boolean_value fvf@395 $r) (invOf@386 $r))
  :pattern (($FVF.lookup_Ref__Boolean_value $t@378 $r) (invOf@386 $r)))))
(assert (forall (($r $Ref)) (!
  (implies
    (and
      (<
        $Perm.No
        (-
          (-
            (ite
              (and (<= 0 (invOf@129 $r)) (< (invOf@129 $r) $t@123))
              $k@127
              $Perm.No)
            ($permsTaken31 $r))
          ($permsTaken33 $r)))
      ($Set.in $r ($FVF.domain_Ref__Boolean_value fvf@395)))
    (=
      ($FVF.lookup_Ref__Boolean_value fvf@395 $r)
      ($FVF.lookup_Ref__Boolean_value $t@128 $r)))
  :pattern (($FVF.lookup_Ref__Boolean_value fvf@395 $r) (invOf@129 $r))
  :pattern (($FVF.lookup_Ref__Boolean_value $t@128 $r) (invOf@129 $r)))))
(assert (forall (($r $Ref)) (!
  (implies
    (and
      (<
        $Perm.No
        (-
          (-
            (ite
              (and (<= 0 (invOf@121 $r)) (< (invOf@121 $r) $t@116))
              $Perm.Write
              $Perm.No)
            ($permsTaken32 $r))
          ($permsTaken34 $r)))
      ($Set.in $r ($FVF.domain_Ref__Boolean_value fvf@395)))
    (=
      ($FVF.lookup_Ref__Boolean_value fvf@395 $r)
      ($FVF.lookup_Ref__Boolean_value $t@120 $r)))
  :pattern (($FVF.lookup_Ref__Boolean_value fvf@395 $r) (invOf@121 $r))
  :pattern (($FVF.lookup_Ref__Boolean_value $t@120 $r) (invOf@121 $r)))))
(pop) ; 8
(push) ; 8
; [else-branch 76] !0 <= k@392 && k@392 < j@272
(assert (not (and (<= 0 k@392) (< k@392 j@272))))
(pop) ; 8
(pop) ; 7
(assert (forall (($r $Ref)) (!
  (implies
    (and
      (<
        $Perm.No
        (-
          (-
            (ite
              (and (<= 0 (invOf@121 $r)) (< (invOf@121 $r) $t@116))
              $Perm.Write
              $Perm.No)
            ($permsTaken32 $r))
          ($permsTaken34 $r)))
      ($Set.in $r ($FVF.domain_Ref__Boolean_value fvf@395)))
    (=
      ($FVF.lookup_Ref__Boolean_value fvf@395 $r)
      ($FVF.lookup_Ref__Boolean_value $t@120 $r)))
  :pattern (($FVF.lookup_Ref__Boolean_value fvf@395 $r) (invOf@121 $r))
  :pattern (($FVF.lookup_Ref__Boolean_value $t@120 $r) (invOf@121 $r)))))
(assert (forall (($r $Ref)) (!
  (implies
    (and
      (<
        $Perm.No
        (-
          (-
            (ite
              (and (<= 0 (invOf@129 $r)) (< (invOf@129 $r) $t@123))
              $k@127
              $Perm.No)
            ($permsTaken31 $r))
          ($permsTaken33 $r)))
      ($Set.in $r ($FVF.domain_Ref__Boolean_value fvf@395)))
    (=
      ($FVF.lookup_Ref__Boolean_value fvf@395 $r)
      ($FVF.lookup_Ref__Boolean_value $t@128 $r)))
  :pattern (($FVF.lookup_Ref__Boolean_value fvf@395 $r) (invOf@129 $r))
  :pattern (($FVF.lookup_Ref__Boolean_value $t@128 $r) (invOf@129 $r)))))
(assert (forall (($r $Ref)) (!
  (implies
    (and
      (and (<= 0 (invOf@386 $r)) (< (invOf@386 $r) $t@382))
      ($Set.in $r ($FVF.domain_Ref__Boolean_value fvf@395)))
    (=
      ($FVF.lookup_Ref__Boolean_value fvf@395 $r)
      ($FVF.lookup_Ref__Boolean_value $t@378 $r)))
  :pattern (($FVF.lookup_Ref__Boolean_value fvf@395 $r) (invOf@386 $r))
  :pattern (($FVF.lookup_Ref__Boolean_value $t@378 $r) (invOf@386 $r)))))
(assert (forall (($r $Ref)) (!
  (implies
    (and
      (ite
        (and (<= 0 (invOf@391 $r)) (< (invOf@391 $r) $t@375))
        (< $Perm.No $k@390)
        false)
      ($Set.in $r ($FVF.domain_Ref__Boolean_value fvf@395)))
    (=
      ($FVF.lookup_Ref__Boolean_value fvf@395 $r)
      ($FVF.lookup_Ref__Boolean_value $t@368 $r)))
  :pattern (($FVF.lookup_Ref__Boolean_value fvf@395 $r) (invOf@391 $r))
  :pattern (($FVF.lookup_Ref__Boolean_value $t@368 $r) (invOf@391 $r)))))
(assert (forall ((k@392 Int)) (!
  (iff
    ($Set.in ($Seq.index $t@372 k@392) ($FVF.domain_Ref__Boolean_value fvf@395))
    (and
      ($FVF.lookup_Ref__Boolean_value fvf@393 ($Seq.index $t@381 k@392))
      (and (<= 0 k@392) (< k@392 j@272))
      (not (<= $t@116 $t@123))))
  :pattern (($Set.in
    ($Seq.index $t@372 k@392)
    ($FVF.domain_Ref__Boolean_value fvf@395))))))
(assert (forall ((k@392 Int)) (!
  (iff
    ($Set.in ($Seq.index $t@381 k@392) ($FVF.domain_Ref__Boolean_value fvf@393))
    (and (and (<= 0 k@392) (< k@392 j@272)) (not (<= $t@116 $t@123))))
  :pattern (($Set.in
    ($Seq.index $t@381 k@392)
    ($FVF.domain_Ref__Boolean_value fvf@393))))))
(assert (forall (($r $Ref)) (!
  (implies
    (and
      (ite
        (and (<= 0 (invOf@391 $r)) (< (invOf@391 $r) $t@375))
        (< $Perm.No $k@390)
        false)
      ($Set.in $r ($FVF.domain_Ref__Boolean_value fvf@393)))
    (=
      ($FVF.lookup_Ref__Boolean_value fvf@393 $r)
      ($FVF.lookup_Ref__Boolean_value $t@368 $r)))
  :pattern (($FVF.lookup_Ref__Boolean_value fvf@393 $r) (invOf@391 $r))
  :pattern (($FVF.lookup_Ref__Boolean_value $t@368 $r) (invOf@391 $r)))))
(assert (forall (($r $Ref)) (!
  (implies
    (and
      (and (<= 0 (invOf@386 $r)) (< (invOf@386 $r) $t@382))
      ($Set.in $r ($FVF.domain_Ref__Boolean_value fvf@393)))
    (=
      ($FVF.lookup_Ref__Boolean_value fvf@393 $r)
      ($FVF.lookup_Ref__Boolean_value $t@378 $r)))
  :pattern (($FVF.lookup_Ref__Boolean_value fvf@393 $r) (invOf@386 $r))
  :pattern (($FVF.lookup_Ref__Boolean_value $t@378 $r) (invOf@386 $r)))))
(assert (forall (($r $Ref)) (!
  (implies
    (and
      (<
        $Perm.No
        (-
          (-
            (ite
              (and (<= 0 (invOf@129 $r)) (< (invOf@129 $r) $t@123))
              $k@127
              $Perm.No)
            ($permsTaken31 $r))
          ($permsTaken33 $r)))
      ($Set.in $r ($FVF.domain_Ref__Boolean_value fvf@393)))
    (=
      ($FVF.lookup_Ref__Boolean_value fvf@393 $r)
      ($FVF.lookup_Ref__Boolean_value $t@128 $r)))
  :pattern (($FVF.lookup_Ref__Boolean_value fvf@393 $r) (invOf@129 $r))
  :pattern (($FVF.lookup_Ref__Boolean_value $t@128 $r) (invOf@129 $r)))))
(assert (forall (($r $Ref)) (!
  (implies
    (and
      (<
        $Perm.No
        (-
          (-
            (ite
              (and (<= 0 (invOf@121 $r)) (< (invOf@121 $r) $t@116))
              $Perm.Write
              $Perm.No)
            ($permsTaken32 $r))
          ($permsTaken34 $r)))
      ($Set.in $r ($FVF.domain_Ref__Boolean_value fvf@393)))
    (=
      ($FVF.lookup_Ref__Boolean_value fvf@393 $r)
      ($FVF.lookup_Ref__Boolean_value $t@120 $r)))
  :pattern (($FVF.lookup_Ref__Boolean_value fvf@393 $r) (invOf@121 $r))
  :pattern (($FVF.lookup_Ref__Boolean_value $t@120 $r) (invOf@121 $r)))))
(pop) ; 6
(assert (forall (($r $Ref)) (!
  (implies
    (and
      (<
        $Perm.No
        (-
          (-
            (ite
              (and (<= 0 (invOf@121 $r)) (< (invOf@121 $r) $t@116))
              $Perm.Write
              $Perm.No)
            ($permsTaken32 $r))
          ($permsTaken34 $r)))
      ($Set.in $r ($FVF.domain_Ref__Boolean_value fvf@395)))
    (=
      ($FVF.lookup_Ref__Boolean_value fvf@395 $r)
      ($FVF.lookup_Ref__Boolean_value $t@120 $r)))
  :pattern (($FVF.lookup_Ref__Boolean_value fvf@395 $r) (invOf@121 $r))
  :pattern (($FVF.lookup_Ref__Boolean_value $t@120 $r) (invOf@121 $r)))))
(assert (forall (($r $Ref)) (!
  (implies
    (and
      (<
        $Perm.No
        (-
          (-
            (ite
              (and (<= 0 (invOf@129 $r)) (< (invOf@129 $r) $t@123))
              $k@127
              $Perm.No)
            ($permsTaken31 $r))
          ($permsTaken33 $r)))
      ($Set.in $r ($FVF.domain_Ref__Boolean_value fvf@395)))
    (=
      ($FVF.lookup_Ref__Boolean_value fvf@395 $r)
      ($FVF.lookup_Ref__Boolean_value $t@128 $r)))
  :pattern (($FVF.lookup_Ref__Boolean_value fvf@395 $r) (invOf@129 $r))
  :pattern (($FVF.lookup_Ref__Boolean_value $t@128 $r) (invOf@129 $r)))))
(assert (forall (($r $Ref)) (!
  (implies
    (and
      (and (<= 0 (invOf@386 $r)) (< (invOf@386 $r) $t@382))
      ($Set.in $r ($FVF.domain_Ref__Boolean_value fvf@395)))
    (=
      ($FVF.lookup_Ref__Boolean_value fvf@395 $r)
      ($FVF.lookup_Ref__Boolean_value $t@378 $r)))
  :pattern (($FVF.lookup_Ref__Boolean_value fvf@395 $r) (invOf@386 $r))
  :pattern (($FVF.lookup_Ref__Boolean_value $t@378 $r) (invOf@386 $r)))))
(assert (forall (($r $Ref)) (!
  (implies
    (and
      (ite
        (and (<= 0 (invOf@391 $r)) (< (invOf@391 $r) $t@375))
        (< $Perm.No $k@390)
        false)
      ($Set.in $r ($FVF.domain_Ref__Boolean_value fvf@395)))
    (=
      ($FVF.lookup_Ref__Boolean_value fvf@395 $r)
      ($FVF.lookup_Ref__Boolean_value $t@368 $r)))
  :pattern (($FVF.lookup_Ref__Boolean_value fvf@395 $r) (invOf@391 $r))
  :pattern (($FVF.lookup_Ref__Boolean_value $t@368 $r) (invOf@391 $r)))))
(assert (forall ((k@392 Int)) (!
  (iff
    ($Set.in ($Seq.index $t@372 k@392) ($FVF.domain_Ref__Boolean_value fvf@395))
    (and
      ($FVF.lookup_Ref__Boolean_value fvf@393 ($Seq.index $t@381 k@392))
      (and (<= 0 k@392) (< k@392 j@272))
      (not (<= $t@116 $t@123))))
  :pattern (($Set.in
    ($Seq.index $t@372 k@392)
    ($FVF.domain_Ref__Boolean_value fvf@395))))))
(assert (forall ((k@392 Int)) (!
  (iff
    ($Set.in ($Seq.index $t@381 k@392) ($FVF.domain_Ref__Boolean_value fvf@393))
    (and (and (<= 0 k@392) (< k@392 j@272)) (not (<= $t@116 $t@123))))
  :pattern (($Set.in
    ($Seq.index $t@381 k@392)
    ($FVF.domain_Ref__Boolean_value fvf@393))))))
(assert (forall (($r $Ref)) (!
  (implies
    (and
      (ite
        (and (<= 0 (invOf@391 $r)) (< (invOf@391 $r) $t@375))
        (< $Perm.No $k@390)
        false)
      ($Set.in $r ($FVF.domain_Ref__Boolean_value fvf@393)))
    (=
      ($FVF.lookup_Ref__Boolean_value fvf@393 $r)
      ($FVF.lookup_Ref__Boolean_value $t@368 $r)))
  :pattern (($FVF.lookup_Ref__Boolean_value fvf@393 $r) (invOf@391 $r))
  :pattern (($FVF.lookup_Ref__Boolean_value $t@368 $r) (invOf@391 $r)))))
(assert (forall (($r $Ref)) (!
  (implies
    (and
      (and (<= 0 (invOf@386 $r)) (< (invOf@386 $r) $t@382))
      ($Set.in $r ($FVF.domain_Ref__Boolean_value fvf@393)))
    (=
      ($FVF.lookup_Ref__Boolean_value fvf@393 $r)
      ($FVF.lookup_Ref__Boolean_value $t@378 $r)))
  :pattern (($FVF.lookup_Ref__Boolean_value fvf@393 $r) (invOf@386 $r))
  :pattern (($FVF.lookup_Ref__Boolean_value $t@378 $r) (invOf@386 $r)))))
(assert (forall (($r $Ref)) (!
  (implies
    (and
      (<
        $Perm.No
        (-
          (-
            (ite
              (and (<= 0 (invOf@129 $r)) (< (invOf@129 $r) $t@123))
              $k@127
              $Perm.No)
            ($permsTaken31 $r))
          ($permsTaken33 $r)))
      ($Set.in $r ($FVF.domain_Ref__Boolean_value fvf@393)))
    (=
      ($FVF.lookup_Ref__Boolean_value fvf@393 $r)
      ($FVF.lookup_Ref__Boolean_value $t@128 $r)))
  :pattern (($FVF.lookup_Ref__Boolean_value fvf@393 $r) (invOf@129 $r))
  :pattern (($FVF.lookup_Ref__Boolean_value $t@128 $r) (invOf@129 $r)))))
(assert (forall (($r $Ref)) (!
  (implies
    (and
      (<
        $Perm.No
        (-
          (-
            (ite
              (and (<= 0 (invOf@121 $r)) (< (invOf@121 $r) $t@116))
              $Perm.Write
              $Perm.No)
            ($permsTaken32 $r))
          ($permsTaken34 $r)))
      ($Set.in $r ($FVF.domain_Ref__Boolean_value fvf@393)))
    (=
      ($FVF.lookup_Ref__Boolean_value fvf@393 $r)
      ($FVF.lookup_Ref__Boolean_value $t@120 $r)))
  :pattern (($FVF.lookup_Ref__Boolean_value fvf@393 $r) (invOf@121 $r))
  :pattern (($FVF.lookup_Ref__Boolean_value $t@120 $r) (invOf@121 $r)))))
(assert (forall ((k@392 Int)) (!
  (implies
    (and (<= 0 k@392) (< k@392 j@272))
    (=
      ($FVF.lookup_Ref__Boolean_value fvf@393 ($Seq.index $t@381 k@392))
      (and
        ($FVF.lookup_Ref__Boolean_value fvf@393 ($Seq.index $t@381 k@392))
        ($FVF.lookup_Ref__Boolean_value fvf@395 ($Seq.index $t@372 k@392)))))
  :pattern (($Seq.index $t@381 k@392))
  :pattern (($Seq.index $t@381 k@392))
  :pattern (($Seq.index $t@372 k@392)))))
; [eval] !(j < x.Set__max)
; [eval] j < x.Set__max
(assert (not (< j@272 $t@375)))
(set-option :timeout 0)
(check-sat)
; unknown
; [exec]
; assert (forall k: Int :: (0 <= k) && (k < x.Set__max) ==> (diz.Set__contents[k].Ref__Boolean_value == diz.Set__contents[k].Ref__Boolean_value && x.Set__contents[k].Ref__Boolean_value))
; [eval] (forall k: Int :: (0 <= k) && (k < x.Set__max) ==> (diz.Set__contents[k].Ref__Boolean_value == diz.Set__contents[k].Ref__Boolean_value && x.Set__contents[k].Ref__Boolean_value))
(declare-const k@396 Int)
(push) ; 6
; [eval] (0 <= k) && (k < x.Set__max) ==> (diz.Set__contents[k].Ref__Boolean_value == diz.Set__contents[k].Ref__Boolean_value && x.Set__contents[k].Ref__Boolean_value)
; [eval] (0 <= k) && (k < x.Set__max)
; [eval] 0 <= k
(push) ; 7
(set-option :timeout 0)
(push) ; 8
(assert (not (not (<= 0 k@396))))
(check-sat)
; unknown
(pop) ; 8
; 0.00s
; (get-info :all-statistics)
(set-option :timeout 0)
(push) ; 8
(assert (not (<= 0 k@396)))
(check-sat)
; unknown
(pop) ; 8
; 0.00s
; (get-info :all-statistics)
(push) ; 8
; [then-branch 78] 0 <= k@396
(assert (<= 0 k@396))
; [eval] k < x.Set__max
(pop) ; 8
(push) ; 8
; [else-branch 78] !0 <= k@396
(assert (not (<= 0 k@396)))
(pop) ; 8
(pop) ; 7
(push) ; 7
(set-option :timeout 0)
(push) ; 8
(assert (not (not (and (<= 0 k@396) (< k@396 $t@375)))))
(check-sat)
; unknown
(pop) ; 8
; 0.00s
; (get-info :all-statistics)
(set-option :timeout 0)
(push) ; 8
(assert (not (and (<= 0 k@396) (< k@396 $t@375))))
(check-sat)
; unknown
(pop) ; 8
; 0.00s
; (get-info :all-statistics)
(push) ; 8
; [then-branch 79] 0 <= k@396 && k@396 < $t@375
(assert (and (<= 0 k@396) (< k@396 $t@375)))
; [eval] diz.Set__contents[k].Ref__Boolean_value == diz.Set__contents[k].Ref__Boolean_value && x.Set__contents[k].Ref__Boolean_value
; [eval] diz.Set__contents[k]
(set-option :timeout 0)
(push) ; 9
(assert (not (not (= ($Seq.index $t@381 k@396) $Ref.null))))
(check-sat)
; unsat
(pop) ; 9
; 0.00s
; (get-info :all-statistics)
(set-option :timeout 0)
(push) ; 9
(assert (not (<
  $Perm.No
  (+
    (+
      (+
        (-
          (-
            (ite
              (and
                (<= 0 (invOf@121 ($Seq.index $t@381 k@396)))
                (< (invOf@121 ($Seq.index $t@381 k@396)) $t@116))
              $Perm.Write
              $Perm.No)
            ($permsTaken32 ($Seq.index $t@381 k@396)))
          ($permsTaken34 ($Seq.index $t@381 k@396)))
        (-
          (-
            (ite
              (and
                (<= 0 (invOf@129 ($Seq.index $t@381 k@396)))
                (< (invOf@129 ($Seq.index $t@381 k@396)) $t@123))
              $k@127
              $Perm.No)
            ($permsTaken31 ($Seq.index $t@381 k@396)))
          ($permsTaken33 ($Seq.index $t@381 k@396))))
      (ite
        (and
          (<= 0 (invOf@386 ($Seq.index $t@381 k@396)))
          (< (invOf@386 ($Seq.index $t@381 k@396)) $t@382))
        $Perm.Write
        $Perm.No))
    (ite
      (and
        (<= 0 (invOf@391 ($Seq.index $t@381 k@396)))
        (< (invOf@391 ($Seq.index $t@381 k@396)) $t@375))
      $k@390
      $Perm.No)))))
(check-sat)
; unsat
(pop) ; 9
; 0.03s
; (get-info :all-statistics)
(declare-const fvf@397 $FVF<Bool>)
(assert (forall (($r $Ref)) (!
  (implies
    (and
      (<
        $Perm.No
        (-
          (-
            (ite
              (and (<= 0 (invOf@121 $r)) (< (invOf@121 $r) $t@116))
              $Perm.Write
              $Perm.No)
            ($permsTaken32 $r))
          ($permsTaken34 $r)))
      ($Set.in $r ($FVF.domain_Ref__Boolean_value fvf@397)))
    (=
      ($FVF.lookup_Ref__Boolean_value fvf@397 $r)
      ($FVF.lookup_Ref__Boolean_value $t@120 $r)))
  :pattern (($FVF.lookup_Ref__Boolean_value fvf@397 $r) (invOf@121 $r))
  :pattern (($FVF.lookup_Ref__Boolean_value $t@120 $r) (invOf@121 $r)))))
(assert (forall (($r $Ref)) (!
  (implies
    (and
      (<
        $Perm.No
        (-
          (-
            (ite
              (and (<= 0 (invOf@129 $r)) (< (invOf@129 $r) $t@123))
              $k@127
              $Perm.No)
            ($permsTaken31 $r))
          ($permsTaken33 $r)))
      ($Set.in $r ($FVF.domain_Ref__Boolean_value fvf@397)))
    (=
      ($FVF.lookup_Ref__Boolean_value fvf@397 $r)
      ($FVF.lookup_Ref__Boolean_value $t@128 $r)))
  :pattern (($FVF.lookup_Ref__Boolean_value fvf@397 $r) (invOf@129 $r))
  :pattern (($FVF.lookup_Ref__Boolean_value $t@128 $r) (invOf@129 $r)))))
(assert (forall (($r $Ref)) (!
  (implies
    (and
      (and (<= 0 (invOf@386 $r)) (< (invOf@386 $r) $t@382))
      ($Set.in $r ($FVF.domain_Ref__Boolean_value fvf@397)))
    (=
      ($FVF.lookup_Ref__Boolean_value fvf@397 $r)
      ($FVF.lookup_Ref__Boolean_value $t@378 $r)))
  :pattern (($FVF.lookup_Ref__Boolean_value fvf@397 $r) (invOf@386 $r))
  :pattern (($FVF.lookup_Ref__Boolean_value $t@378 $r) (invOf@386 $r)))))
(assert (forall (($r $Ref)) (!
  (implies
    (and
      (ite
        (and (<= 0 (invOf@391 $r)) (< (invOf@391 $r) $t@375))
        (< $Perm.No $k@390)
        false)
      ($Set.in $r ($FVF.domain_Ref__Boolean_value fvf@397)))
    (=
      ($FVF.lookup_Ref__Boolean_value fvf@397 $r)
      ($FVF.lookup_Ref__Boolean_value $t@368 $r)))
  :pattern (($FVF.lookup_Ref__Boolean_value fvf@397 $r) (invOf@391 $r))
  :pattern (($FVF.lookup_Ref__Boolean_value $t@368 $r) (invOf@391 $r)))))
(assert (forall ((k@396 Int)) (!
  (iff
    ($Set.in ($Seq.index $t@381 k@396) ($FVF.domain_Ref__Boolean_value fvf@397))
    (and (and (<= 0 k@396) (< k@396 $t@375)) (not (<= $t@116 $t@123))))
  :pattern (($Set.in
    ($Seq.index $t@381 k@396)
    ($FVF.domain_Ref__Boolean_value fvf@397))))))
; [eval] diz.Set__contents[k].Ref__Boolean_value && x.Set__contents[k].Ref__Boolean_value
; [eval] diz.Set__contents[k]
(set-option :timeout 0)
(push) ; 9
(assert (not (not (= ($Seq.index $t@381 k@396) $Ref.null))))
(check-sat)
; unsat
(pop) ; 9
; 0.00s
; (get-info :all-statistics)
(set-option :timeout 0)
(push) ; 9
(assert (not (<
  $Perm.No
  (+
    (+
      (+
        (-
          (-
            (ite
              (and
                (<= 0 (invOf@121 ($Seq.index $t@381 k@396)))
                (< (invOf@121 ($Seq.index $t@381 k@396)) $t@116))
              $Perm.Write
              $Perm.No)
            ($permsTaken32 ($Seq.index $t@381 k@396)))
          ($permsTaken34 ($Seq.index $t@381 k@396)))
        (-
          (-
            (ite
              (and
                (<= 0 (invOf@129 ($Seq.index $t@381 k@396)))
                (< (invOf@129 ($Seq.index $t@381 k@396)) $t@123))
              $k@127
              $Perm.No)
            ($permsTaken31 ($Seq.index $t@381 k@396)))
          ($permsTaken33 ($Seq.index $t@381 k@396))))
      (ite
        (and
          (<= 0 (invOf@386 ($Seq.index $t@381 k@396)))
          (< (invOf@386 ($Seq.index $t@381 k@396)) $t@382))
        $Perm.Write
        $Perm.No))
    (ite
      (and
        (<= 0 (invOf@391 ($Seq.index $t@381 k@396)))
        (< (invOf@391 ($Seq.index $t@381 k@396)) $t@375))
      $k@390
      $Perm.No)))))
(check-sat)
; unsat
(pop) ; 9
; 0.03s
; (get-info :all-statistics)
(declare-const fvf@398 $FVF<Bool>)
(push) ; 9
(set-option :timeout 0)
(push) ; 10
(assert (not (not ($FVF.lookup_Ref__Boolean_value fvf@397 ($Seq.index $t@381 k@396)))))
(check-sat)
; unknown
(pop) ; 10
; 1.73s
; (get-info :all-statistics)
(set-option :timeout 0)
(push) ; 10
(assert (not ($FVF.lookup_Ref__Boolean_value fvf@397 ($Seq.index $t@381 k@396))))
(check-sat)
; unknown
(pop) ; 10
; 0.06s
; (get-info :all-statistics)
(push) ; 10
; [then-branch 80] Lookup(Ref__Boolean_value,fvf@397,$t@381[k@396])
(assert ($FVF.lookup_Ref__Boolean_value fvf@397 ($Seq.index $t@381 k@396)))
; [eval] x.Set__contents[k]
(set-option :timeout 0)
(push) ; 11
(assert (not (not (= ($Seq.index $t@372 k@396) $Ref.null))))
(check-sat)
; unsat
(pop) ; 11
; 0.00s
; (get-info :all-statistics)
(set-option :timeout 0)
(push) ; 11
(assert (not (<
  $Perm.No
  (+
    (+
      (+
        (-
          (-
            (ite
              (and
                (<= 0 (invOf@121 ($Seq.index $t@372 k@396)))
                (< (invOf@121 ($Seq.index $t@372 k@396)) $t@116))
              $Perm.Write
              $Perm.No)
            ($permsTaken32 ($Seq.index $t@372 k@396)))
          ($permsTaken34 ($Seq.index $t@372 k@396)))
        (-
          (-
            (ite
              (and
                (<= 0 (invOf@129 ($Seq.index $t@372 k@396)))
                (< (invOf@129 ($Seq.index $t@372 k@396)) $t@123))
              $k@127
              $Perm.No)
            ($permsTaken31 ($Seq.index $t@372 k@396)))
          ($permsTaken33 ($Seq.index $t@372 k@396))))
      (ite
        (and
          (<= 0 (invOf@386 ($Seq.index $t@372 k@396)))
          (< (invOf@386 ($Seq.index $t@372 k@396)) $t@382))
        $Perm.Write
        $Perm.No))
    (ite
      (and
        (<= 0 (invOf@391 ($Seq.index $t@372 k@396)))
        (< (invOf@391 ($Seq.index $t@372 k@396)) $t@375))
      $k@390
      $Perm.No)))))
(check-sat)
; unsat
(pop) ; 11
; 0.03s
; (get-info :all-statistics)
(declare-const fvf@399 $FVF<Bool>)
(assert (forall (($r $Ref)) (!
  (implies
    (and
      (<
        $Perm.No
        (-
          (-
            (ite
              (and (<= 0 (invOf@121 $r)) (< (invOf@121 $r) $t@116))
              $Perm.Write
              $Perm.No)
            ($permsTaken32 $r))
          ($permsTaken34 $r)))
      ($Set.in $r ($FVF.domain_Ref__Boolean_value fvf@399)))
    (=
      ($FVF.lookup_Ref__Boolean_value fvf@399 $r)
      ($FVF.lookup_Ref__Boolean_value $t@120 $r)))
  :pattern (($FVF.lookup_Ref__Boolean_value fvf@399 $r) (invOf@121 $r))
  :pattern (($FVF.lookup_Ref__Boolean_value $t@120 $r) (invOf@121 $r)))))
(assert (forall (($r $Ref)) (!
  (implies
    (and
      (<
        $Perm.No
        (-
          (-
            (ite
              (and (<= 0 (invOf@129 $r)) (< (invOf@129 $r) $t@123))
              $k@127
              $Perm.No)
            ($permsTaken31 $r))
          ($permsTaken33 $r)))
      ($Set.in $r ($FVF.domain_Ref__Boolean_value fvf@399)))
    (=
      ($FVF.lookup_Ref__Boolean_value fvf@399 $r)
      ($FVF.lookup_Ref__Boolean_value $t@128 $r)))
  :pattern (($FVF.lookup_Ref__Boolean_value fvf@399 $r) (invOf@129 $r))
  :pattern (($FVF.lookup_Ref__Boolean_value $t@128 $r) (invOf@129 $r)))))
(assert (forall (($r $Ref)) (!
  (implies
    (and
      (and (<= 0 (invOf@386 $r)) (< (invOf@386 $r) $t@382))
      ($Set.in $r ($FVF.domain_Ref__Boolean_value fvf@399)))
    (=
      ($FVF.lookup_Ref__Boolean_value fvf@399 $r)
      ($FVF.lookup_Ref__Boolean_value $t@378 $r)))
  :pattern (($FVF.lookup_Ref__Boolean_value fvf@399 $r) (invOf@386 $r))
  :pattern (($FVF.lookup_Ref__Boolean_value $t@378 $r) (invOf@386 $r)))))
(assert (forall (($r $Ref)) (!
  (implies
    (and
      (ite
        (and (<= 0 (invOf@391 $r)) (< (invOf@391 $r) $t@375))
        (< $Perm.No $k@390)
        false)
      ($Set.in $r ($FVF.domain_Ref__Boolean_value fvf@399)))
    (=
      ($FVF.lookup_Ref__Boolean_value fvf@399 $r)
      ($FVF.lookup_Ref__Boolean_value $t@368 $r)))
  :pattern (($FVF.lookup_Ref__Boolean_value fvf@399 $r) (invOf@391 $r))
  :pattern (($FVF.lookup_Ref__Boolean_value $t@368 $r) (invOf@391 $r)))))
(assert (forall ((k@396 Int)) (!
  (iff
    ($Set.in ($Seq.index $t@372 k@396) ($FVF.domain_Ref__Boolean_value fvf@399))
    (and
      ($FVF.lookup_Ref__Boolean_value fvf@397 ($Seq.index $t@381 k@396))
      (and (<= 0 k@396) (< k@396 $t@375))
      (not (<= $t@116 $t@123))))
  :pattern (($Set.in
    ($Seq.index $t@372 k@396)
    ($FVF.domain_Ref__Boolean_value fvf@399))))))
(pop) ; 10
(push) ; 10
; [else-branch 80] !Lookup(Ref__Boolean_value,fvf@397,$t@381[k@396])
(assert (not ($FVF.lookup_Ref__Boolean_value fvf@397 ($Seq.index $t@381 k@396))))
(pop) ; 10
(pop) ; 9
(assert (forall ((k@396 Int)) (!
  (iff
    ($Set.in ($Seq.index $t@372 k@396) ($FVF.domain_Ref__Boolean_value fvf@399))
    (and
      ($FVF.lookup_Ref__Boolean_value fvf@397 ($Seq.index $t@381 k@396))
      (and (<= 0 k@396) (< k@396 $t@375))
      (not (<= $t@116 $t@123))))
  :pattern (($Set.in
    ($Seq.index $t@372 k@396)
    ($FVF.domain_Ref__Boolean_value fvf@399))))))
(assert (forall (($r $Ref)) (!
  (implies
    (and
      (ite
        (and (<= 0 (invOf@391 $r)) (< (invOf@391 $r) $t@375))
        (< $Perm.No $k@390)
        false)
      ($Set.in $r ($FVF.domain_Ref__Boolean_value fvf@399)))
    (=
      ($FVF.lookup_Ref__Boolean_value fvf@399 $r)
      ($FVF.lookup_Ref__Boolean_value $t@368 $r)))
  :pattern (($FVF.lookup_Ref__Boolean_value fvf@399 $r) (invOf@391 $r))
  :pattern (($FVF.lookup_Ref__Boolean_value $t@368 $r) (invOf@391 $r)))))
(assert (forall (($r $Ref)) (!
  (implies
    (and
      (and (<= 0 (invOf@386 $r)) (< (invOf@386 $r) $t@382))
      ($Set.in $r ($FVF.domain_Ref__Boolean_value fvf@399)))
    (=
      ($FVF.lookup_Ref__Boolean_value fvf@399 $r)
      ($FVF.lookup_Ref__Boolean_value $t@378 $r)))
  :pattern (($FVF.lookup_Ref__Boolean_value fvf@399 $r) (invOf@386 $r))
  :pattern (($FVF.lookup_Ref__Boolean_value $t@378 $r) (invOf@386 $r)))))
(assert (forall (($r $Ref)) (!
  (implies
    (and
      (<
        $Perm.No
        (-
          (-
            (ite
              (and (<= 0 (invOf@129 $r)) (< (invOf@129 $r) $t@123))
              $k@127
              $Perm.No)
            ($permsTaken31 $r))
          ($permsTaken33 $r)))
      ($Set.in $r ($FVF.domain_Ref__Boolean_value fvf@399)))
    (=
      ($FVF.lookup_Ref__Boolean_value fvf@399 $r)
      ($FVF.lookup_Ref__Boolean_value $t@128 $r)))
  :pattern (($FVF.lookup_Ref__Boolean_value fvf@399 $r) (invOf@129 $r))
  :pattern (($FVF.lookup_Ref__Boolean_value $t@128 $r) (invOf@129 $r)))))
(assert (forall (($r $Ref)) (!
  (implies
    (and
      (<
        $Perm.No
        (-
          (-
            (ite
              (and (<= 0 (invOf@121 $r)) (< (invOf@121 $r) $t@116))
              $Perm.Write
              $Perm.No)
            ($permsTaken32 $r))
          ($permsTaken34 $r)))
      ($Set.in $r ($FVF.domain_Ref__Boolean_value fvf@399)))
    (=
      ($FVF.lookup_Ref__Boolean_value fvf@399 $r)
      ($FVF.lookup_Ref__Boolean_value $t@120 $r)))
  :pattern (($FVF.lookup_Ref__Boolean_value fvf@399 $r) (invOf@121 $r))
  :pattern (($FVF.lookup_Ref__Boolean_value $t@120 $r) (invOf@121 $r)))))
(pop) ; 8
(push) ; 8
; [else-branch 79] !0 <= k@396 && k@396 < $t@375
(assert (not (and (<= 0 k@396) (< k@396 $t@375))))
(pop) ; 8
(pop) ; 7
(assert (forall (($r $Ref)) (!
  (implies
    (and
      (<
        $Perm.No
        (-
          (-
            (ite
              (and (<= 0 (invOf@121 $r)) (< (invOf@121 $r) $t@116))
              $Perm.Write
              $Perm.No)
            ($permsTaken32 $r))
          ($permsTaken34 $r)))
      ($Set.in $r ($FVF.domain_Ref__Boolean_value fvf@399)))
    (=
      ($FVF.lookup_Ref__Boolean_value fvf@399 $r)
      ($FVF.lookup_Ref__Boolean_value $t@120 $r)))
  :pattern (($FVF.lookup_Ref__Boolean_value fvf@399 $r) (invOf@121 $r))
  :pattern (($FVF.lookup_Ref__Boolean_value $t@120 $r) (invOf@121 $r)))))
(assert (forall (($r $Ref)) (!
  (implies
    (and
      (<
        $Perm.No
        (-
          (-
            (ite
              (and (<= 0 (invOf@129 $r)) (< (invOf@129 $r) $t@123))
              $k@127
              $Perm.No)
            ($permsTaken31 $r))
          ($permsTaken33 $r)))
      ($Set.in $r ($FVF.domain_Ref__Boolean_value fvf@399)))
    (=
      ($FVF.lookup_Ref__Boolean_value fvf@399 $r)
      ($FVF.lookup_Ref__Boolean_value $t@128 $r)))
  :pattern (($FVF.lookup_Ref__Boolean_value fvf@399 $r) (invOf@129 $r))
  :pattern (($FVF.lookup_Ref__Boolean_value $t@128 $r) (invOf@129 $r)))))
(assert (forall (($r $Ref)) (!
  (implies
    (and
      (and (<= 0 (invOf@386 $r)) (< (invOf@386 $r) $t@382))
      ($Set.in $r ($FVF.domain_Ref__Boolean_value fvf@399)))
    (=
      ($FVF.lookup_Ref__Boolean_value fvf@399 $r)
      ($FVF.lookup_Ref__Boolean_value $t@378 $r)))
  :pattern (($FVF.lookup_Ref__Boolean_value fvf@399 $r) (invOf@386 $r))
  :pattern (($FVF.lookup_Ref__Boolean_value $t@378 $r) (invOf@386 $r)))))
(assert (forall (($r $Ref)) (!
  (implies
    (and
      (ite
        (and (<= 0 (invOf@391 $r)) (< (invOf@391 $r) $t@375))
        (< $Perm.No $k@390)
        false)
      ($Set.in $r ($FVF.domain_Ref__Boolean_value fvf@399)))
    (=
      ($FVF.lookup_Ref__Boolean_value fvf@399 $r)
      ($FVF.lookup_Ref__Boolean_value $t@368 $r)))
  :pattern (($FVF.lookup_Ref__Boolean_value fvf@399 $r) (invOf@391 $r))
  :pattern (($FVF.lookup_Ref__Boolean_value $t@368 $r) (invOf@391 $r)))))
(assert (forall ((k@396 Int)) (!
  (iff
    ($Set.in ($Seq.index $t@372 k@396) ($FVF.domain_Ref__Boolean_value fvf@399))
    (and
      ($FVF.lookup_Ref__Boolean_value fvf@397 ($Seq.index $t@381 k@396))
      (and (<= 0 k@396) (< k@396 $t@375))
      (not (<= $t@116 $t@123))))
  :pattern (($Set.in
    ($Seq.index $t@372 k@396)
    ($FVF.domain_Ref__Boolean_value fvf@399))))))
(assert (forall ((k@396 Int)) (!
  (iff
    ($Set.in ($Seq.index $t@381 k@396) ($FVF.domain_Ref__Boolean_value fvf@397))
    (and (and (<= 0 k@396) (< k@396 $t@375)) (not (<= $t@116 $t@123))))
  :pattern (($Set.in
    ($Seq.index $t@381 k@396)
    ($FVF.domain_Ref__Boolean_value fvf@397))))))
(assert (forall (($r $Ref)) (!
  (implies
    (and
      (ite
        (and (<= 0 (invOf@391 $r)) (< (invOf@391 $r) $t@375))
        (< $Perm.No $k@390)
        false)
      ($Set.in $r ($FVF.domain_Ref__Boolean_value fvf@397)))
    (=
      ($FVF.lookup_Ref__Boolean_value fvf@397 $r)
      ($FVF.lookup_Ref__Boolean_value $t@368 $r)))
  :pattern (($FVF.lookup_Ref__Boolean_value fvf@397 $r) (invOf@391 $r))
  :pattern (($FVF.lookup_Ref__Boolean_value $t@368 $r) (invOf@391 $r)))))
(assert (forall (($r $Ref)) (!
  (implies
    (and
      (and (<= 0 (invOf@386 $r)) (< (invOf@386 $r) $t@382))
      ($Set.in $r ($FVF.domain_Ref__Boolean_value fvf@397)))
    (=
      ($FVF.lookup_Ref__Boolean_value fvf@397 $r)
      ($FVF.lookup_Ref__Boolean_value $t@378 $r)))
  :pattern (($FVF.lookup_Ref__Boolean_value fvf@397 $r) (invOf@386 $r))
  :pattern (($FVF.lookup_Ref__Boolean_value $t@378 $r) (invOf@386 $r)))))
(assert (forall (($r $Ref)) (!
  (implies
    (and
      (<
        $Perm.No
        (-
          (-
            (ite
              (and (<= 0 (invOf@129 $r)) (< (invOf@129 $r) $t@123))
              $k@127
              $Perm.No)
            ($permsTaken31 $r))
          ($permsTaken33 $r)))
      ($Set.in $r ($FVF.domain_Ref__Boolean_value fvf@397)))
    (=
      ($FVF.lookup_Ref__Boolean_value fvf@397 $r)
      ($FVF.lookup_Ref__Boolean_value $t@128 $r)))
  :pattern (($FVF.lookup_Ref__Boolean_value fvf@397 $r) (invOf@129 $r))
  :pattern (($FVF.lookup_Ref__Boolean_value $t@128 $r) (invOf@129 $r)))))
(assert (forall (($r $Ref)) (!
  (implies
    (and
      (<
        $Perm.No
        (-
          (-
            (ite
              (and (<= 0 (invOf@121 $r)) (< (invOf@121 $r) $t@116))
              $Perm.Write
              $Perm.No)
            ($permsTaken32 $r))
          ($permsTaken34 $r)))
      ($Set.in $r ($FVF.domain_Ref__Boolean_value fvf@397)))
    (=
      ($FVF.lookup_Ref__Boolean_value fvf@397 $r)
      ($FVF.lookup_Ref__Boolean_value $t@120 $r)))
  :pattern (($FVF.lookup_Ref__Boolean_value fvf@397 $r) (invOf@121 $r))
  :pattern (($FVF.lookup_Ref__Boolean_value $t@120 $r) (invOf@121 $r)))))
(pop) ; 6
(assert (forall (($r $Ref)) (!
  (implies
    (and
      (<
        $Perm.No
        (-
          (-
            (ite
              (and (<= 0 (invOf@121 $r)) (< (invOf@121 $r) $t@116))
              $Perm.Write
              $Perm.No)
            ($permsTaken32 $r))
          ($permsTaken34 $r)))
      ($Set.in $r ($FVF.domain_Ref__Boolean_value fvf@399)))
    (=
      ($FVF.lookup_Ref__Boolean_value fvf@399 $r)
      ($FVF.lookup_Ref__Boolean_value $t@120 $r)))
  :pattern (($FVF.lookup_Ref__Boolean_value fvf@399 $r) (invOf@121 $r))
  :pattern (($FVF.lookup_Ref__Boolean_value $t@120 $r) (invOf@121 $r)))))
(assert (forall (($r $Ref)) (!
  (implies
    (and
      (<
        $Perm.No
        (-
          (-
            (ite
              (and (<= 0 (invOf@129 $r)) (< (invOf@129 $r) $t@123))
              $k@127
              $Perm.No)
            ($permsTaken31 $r))
          ($permsTaken33 $r)))
      ($Set.in $r ($FVF.domain_Ref__Boolean_value fvf@399)))
    (=
      ($FVF.lookup_Ref__Boolean_value fvf@399 $r)
      ($FVF.lookup_Ref__Boolean_value $t@128 $r)))
  :pattern (($FVF.lookup_Ref__Boolean_value fvf@399 $r) (invOf@129 $r))
  :pattern (($FVF.lookup_Ref__Boolean_value $t@128 $r) (invOf@129 $r)))))
(assert (forall (($r $Ref)) (!
  (implies
    (and
      (and (<= 0 (invOf@386 $r)) (< (invOf@386 $r) $t@382))
      ($Set.in $r ($FVF.domain_Ref__Boolean_value fvf@399)))
    (=
      ($FVF.lookup_Ref__Boolean_value fvf@399 $r)
      ($FVF.lookup_Ref__Boolean_value $t@378 $r)))
  :pattern (($FVF.lookup_Ref__Boolean_value fvf@399 $r) (invOf@386 $r))
  :pattern (($FVF.lookup_Ref__Boolean_value $t@378 $r) (invOf@386 $r)))))
(assert (forall (($r $Ref)) (!
  (implies
    (and
      (ite
        (and (<= 0 (invOf@391 $r)) (< (invOf@391 $r) $t@375))
        (< $Perm.No $k@390)
        false)
      ($Set.in $r ($FVF.domain_Ref__Boolean_value fvf@399)))
    (=
      ($FVF.lookup_Ref__Boolean_value fvf@399 $r)
      ($FVF.lookup_Ref__Boolean_value $t@368 $r)))
  :pattern (($FVF.lookup_Ref__Boolean_value fvf@399 $r) (invOf@391 $r))
  :pattern (($FVF.lookup_Ref__Boolean_value $t@368 $r) (invOf@391 $r)))))
(assert (forall ((k@396 Int)) (!
  (iff
    ($Set.in ($Seq.index $t@372 k@396) ($FVF.domain_Ref__Boolean_value fvf@399))
    (and
      ($FVF.lookup_Ref__Boolean_value fvf@397 ($Seq.index $t@381 k@396))
      (and (<= 0 k@396) (< k@396 $t@375))
      (not (<= $t@116 $t@123))))
  :pattern (($Set.in
    ($Seq.index $t@372 k@396)
    ($FVF.domain_Ref__Boolean_value fvf@399))))))
(assert (forall ((k@396 Int)) (!
  (iff
    ($Set.in ($Seq.index $t@381 k@396) ($FVF.domain_Ref__Boolean_value fvf@397))
    (and (and (<= 0 k@396) (< k@396 $t@375)) (not (<= $t@116 $t@123))))
  :pattern (($Set.in
    ($Seq.index $t@381 k@396)
    ($FVF.domain_Ref__Boolean_value fvf@397))))))
(assert (forall (($r $Ref)) (!
  (implies
    (and
      (ite
        (and (<= 0 (invOf@391 $r)) (< (invOf@391 $r) $t@375))
        (< $Perm.No $k@390)
        false)
      ($Set.in $r ($FVF.domain_Ref__Boolean_value fvf@397)))
    (=
      ($FVF.lookup_Ref__Boolean_value fvf@397 $r)
      ($FVF.lookup_Ref__Boolean_value $t@368 $r)))
  :pattern (($FVF.lookup_Ref__Boolean_value fvf@397 $r) (invOf@391 $r))
  :pattern (($FVF.lookup_Ref__Boolean_value $t@368 $r) (invOf@391 $r)))))
(assert (forall (($r $Ref)) (!
  (implies
    (and
      (and (<= 0 (invOf@386 $r)) (< (invOf@386 $r) $t@382))
      ($Set.in $r ($FVF.domain_Ref__Boolean_value fvf@397)))
    (=
      ($FVF.lookup_Ref__Boolean_value fvf@397 $r)
      ($FVF.lookup_Ref__Boolean_value $t@378 $r)))
  :pattern (($FVF.lookup_Ref__Boolean_value fvf@397 $r) (invOf@386 $r))
  :pattern (($FVF.lookup_Ref__Boolean_value $t@378 $r) (invOf@386 $r)))))
(assert (forall (($r $Ref)) (!
  (implies
    (and
      (<
        $Perm.No
        (-
          (-
            (ite
              (and (<= 0 (invOf@129 $r)) (< (invOf@129 $r) $t@123))
              $k@127
              $Perm.No)
            ($permsTaken31 $r))
          ($permsTaken33 $r)))
      ($Set.in $r ($FVF.domain_Ref__Boolean_value fvf@397)))
    (=
      ($FVF.lookup_Ref__Boolean_value fvf@397 $r)
      ($FVF.lookup_Ref__Boolean_value $t@128 $r)))
  :pattern (($FVF.lookup_Ref__Boolean_value fvf@397 $r) (invOf@129 $r))
  :pattern (($FVF.lookup_Ref__Boolean_value $t@128 $r) (invOf@129 $r)))))
(assert (forall (($r $Ref)) (!
  (implies
    (and
      (<
        $Perm.No
        (-
          (-
            (ite
              (and (<= 0 (invOf@121 $r)) (< (invOf@121 $r) $t@116))
              $Perm.Write
              $Perm.No)
            ($permsTaken32 $r))
          ($permsTaken34 $r)))
      ($Set.in $r ($FVF.domain_Ref__Boolean_value fvf@397)))
    (=
      ($FVF.lookup_Ref__Boolean_value fvf@397 $r)
      ($FVF.lookup_Ref__Boolean_value $t@120 $r)))
  :pattern (($FVF.lookup_Ref__Boolean_value fvf@397 $r) (invOf@121 $r))
  :pattern (($FVF.lookup_Ref__Boolean_value $t@120 $r) (invOf@121 $r)))))
(set-option :timeout 0)
(push) ; 6
(assert (not (forall ((k@396 Int)) (!
  (implies
    (and (<= 0 k@396) (< k@396 $t@375))
    (=
      ($FVF.lookup_Ref__Boolean_value fvf@397 ($Seq.index $t@381 k@396))
      (and
        ($FVF.lookup_Ref__Boolean_value fvf@397 ($Seq.index $t@381 k@396))
        ($FVF.lookup_Ref__Boolean_value fvf@399 ($Seq.index $t@372 k@396)))))
  :pattern (($Seq.index $t@381 k@396))
  :pattern (($Seq.index $t@381 k@396))
  :pattern (($Seq.index $t@372 k@396))))))
(check-sat)
; unsat
(pop) ; 6
; 0.01s
; (get-info :all-statistics)
(assert (forall ((k@396 Int)) (!
  (implies
    (and (<= 0 k@396) (< k@396 $t@375))
    (=
      ($FVF.lookup_Ref__Boolean_value fvf@397 ($Seq.index $t@381 k@396))
      (and
        ($FVF.lookup_Ref__Boolean_value fvf@397 ($Seq.index $t@381 k@396))
        ($FVF.lookup_Ref__Boolean_value fvf@399 ($Seq.index $t@372 k@396)))))
  :pattern (($Seq.index $t@381 k@396))
  :pattern (($Seq.index $t@381 k@396))
  :pattern (($Seq.index $t@372 k@396)))))
; loop at <no position>
(declare-const j@400 Int)
(declare-const __flatten_17@401 Bool)
(declare-const __flatten_16@402 $Ref)
(push) ; 6
; Verify loop body
(declare-const $t@403 $Snap)
(declare-const $t@404 $Snap)
(assert (= $t@403 ($Snap.combine $t@404 $Snap.unit)))
(declare-const $t@405 $Snap)
(assert (= $t@404 ($Snap.combine $t@405 $Snap.unit)))
(declare-const $t@406 $Snap)
(declare-const $t@407 $FVF<Bool>)
(assert (= $t@405 ($Snap.combine $t@406 ($SortWrappers.$FVF<Bool>To$Snap $t@407))))
(declare-const $t@408 $Snap)
(assert (= $t@406 ($Snap.combine $t@408 $Snap.unit)))
(declare-const $t@409 $Snap)
(assert (= $t@408 ($Snap.combine $t@409 $Snap.unit)))
(declare-const $t@410 $Snap)
(declare-const $t@411 $Seq<$Ref>)
(assert (= $t@409 ($Snap.combine $t@410 ($SortWrappers.$Seq<$Ref>To$Snap $t@411))))
(declare-const $t@412 $Snap)
(assert (= $t@410 ($Snap.combine $t@412 $Snap.unit)))
(declare-const $t@413 $Snap)
(declare-const $t@414 Int)
(assert (= $t@412 ($Snap.combine $t@413 ($SortWrappers.IntTo$Snap $t@414))))
(declare-const $t@415 $Snap)
(assert (= $t@413 ($Snap.combine $t@415 $Snap.unit)))
(declare-const $t@416 $Snap)
(declare-const $t@417 $FVF<Bool>)
(assert (= $t@415 ($Snap.combine $t@416 ($SortWrappers.$FVF<Bool>To$Snap $t@417))))
(declare-const $t@418 $Snap)
(assert (= $t@416 ($Snap.combine $t@418 $Snap.unit)))
(declare-const $t@419 Int)
(declare-const $t@420 $Seq<$Ref>)
(assert (=
  $t@418
  ($Snap.combine
    ($SortWrappers.IntTo$Snap $t@419)
    ($SortWrappers.$Seq<$Ref>To$Snap $t@420))))
(declare-const $t@421 Int)
(assert (=
  ($SortWrappers.IntTo$Snap $t@419)
  ($Snap.combine ($SortWrappers.IntTo$Snap $t@421) $Snap.unit)))
(declare-const $k@422 $Perm)
(assert ($Perm.isValidVar $k@422))
(assert ($Perm.isReadVar $k@422 $Perm.Write))
; [eval] diz.Set__max > 0
(set-option :timeout 0)
(push) ; 7
(assert (not (not (= $k@422 $Perm.No))))
(check-sat)
; unsat
(pop) ; 7
; 0.00s
; (get-info :all-statistics)
(assert (not (= $k@422 $Perm.No)))
(assert (> $t@421 0))
(declare-const $k@423 $Perm)
(assert ($Perm.isValidVar $k@423))
(assert ($Perm.isReadVar $k@423 $Perm.Write))
; [eval] |diz.Set__contents| == diz.Set__max
; [eval] |diz.Set__contents|
(set-option :timeout 0)
(push) ; 7
(assert (not (not (= $k@423 $Perm.No))))
(check-sat)
; unsat
(pop) ; 7
; 0.00s
; (get-info :all-statistics)
(assert (not (= $k@423 $Perm.No)))
(assert (= ($Seq.length $t@420) $t@421))
(declare-const k@424 Int)
(push) ; 7
; [eval] (0 <= k) && (k < diz.Set__max)
; [eval] 0 <= k
(push) ; 8
(set-option :timeout 0)
(push) ; 9
(assert (not (not (<= 0 k@424))))
(check-sat)
; unknown
(pop) ; 9
; 0.01s
; (get-info :all-statistics)
(set-option :timeout 0)
(push) ; 9
(assert (not (<= 0 k@424)))
(check-sat)
; unknown
(pop) ; 9
; 0.01s
; (get-info :all-statistics)
(push) ; 9
; [then-branch 81] 0 <= k@424
(assert (<= 0 k@424))
; [eval] k < diz.Set__max
(pop) ; 9
(push) ; 9
; [else-branch 81] !0 <= k@424
(assert (not (<= 0 k@424)))
(pop) ; 9
(pop) ; 8
(assert (and (<= 0 k@424) (< k@424 $t@421)))
; [eval] diz.Set__contents[k]
(pop) ; 7
(declare-fun invOf@425 ($Ref) Int)
(assert (forall (($r $Ref)) (!
  (implies
    (and (<= 0 (invOf@425 $r)) (< (invOf@425 $r) $t@421))
    (= ($Seq.index $t@420 (invOf@425 $r)) $r))
  :pattern ((invOf@425 $r)))))
(assert (forall ((k@424 Int)) (!
  (implies
    (and (<= 0 k@424) (< k@424 $t@421))
    (= (invOf@425 ($Seq.index $t@420 k@424)) k@424))
  :pattern (($Seq.index $t@420 k@424)))))
(assert (forall ((k@424 Int)) (!
  (iff
    ($Set.in ($Seq.index $t@420 k@424) ($FVF.domain_Ref__Boolean_value $t@417))
    (and (<= 0 k@424) (< k@424 $t@421)))
  :pattern (($Set.in
    ($Seq.index $t@420 k@424)
    ($FVF.domain_Ref__Boolean_value $t@417))))))
(assert (forall ((k@424 Int)) (!
  (implies
    (and (<= 0 k@424) (< k@424 $t@421))
    (not (= ($Seq.index $t@420 k@424) $Ref.null)))
  :pattern (($Seq.index $t@420 k@424)))))
; [eval] x != null
(declare-const $k@426 $Perm)
(assert ($Perm.isValidVar $k@426))
(assert ($Perm.isReadVar $k@426 $Perm.Write))
(set-option :timeout 0)
(push) ; 7
(assert (not (= diz@101 x@102)))
(check-sat)
; unknown
(pop) ; 7
; 0.01s
; (get-info :all-statistics)
; [eval] x.Set__max > 0
(set-option :timeout 0)
(push) ; 7
(assert (not (not (= $k@426 $Perm.No))))
(check-sat)
; unsat
(pop) ; 7
; 0.00s
; (get-info :all-statistics)
(assert (not (= $k@426 $Perm.No)))
(assert (> $t@414 0))
(declare-const $k@427 $Perm)
(assert ($Perm.isValidVar $k@427))
(assert ($Perm.isReadVar $k@427 $Perm.Write))
(set-option :timeout 0)
(push) ; 7
(assert (not (= diz@101 x@102)))
(check-sat)
; unknown
(pop) ; 7
; 0.01s
; (get-info :all-statistics)
; [eval] diz.Set__max > x.Set__max
(assert (> $t@421 $t@414))
; [eval] (j >= x.Set__max) && (j <= diz.Set__max)
; [eval] j >= x.Set__max
(push) ; 7
(set-option :timeout 0)
(push) ; 8
(assert (not (not (>= j@400 $t@414))))
(check-sat)
; unknown
(pop) ; 8
; 0.01s
; (get-info :all-statistics)
(set-option :timeout 0)
(push) ; 8
(assert (not (>= j@400 $t@414)))
(check-sat)
; unknown
(pop) ; 8
; 0.01s
; (get-info :all-statistics)
(push) ; 8
; [then-branch 82] j@400 >= $t@414
(assert (>= j@400 $t@414))
; [eval] j <= diz.Set__max
(pop) ; 8
(push) ; 8
; [else-branch 82] !j@400 >= $t@414
(assert (not (>= j@400 $t@414)))
(pop) ; 8
(pop) ; 7
(assert (and (>= j@400 $t@414) (<= j@400 $t@421)))
(declare-const k@428 Int)
(push) ; 7
; [eval] (0 <= k) && (k < x.Set__max)
; [eval] 0 <= k
(push) ; 8
(set-option :timeout 0)
(push) ; 9
(assert (not (not (<= 0 k@428))))
(check-sat)
; unknown
(pop) ; 9
; 0.01s
; (get-info :all-statistics)
(set-option :timeout 0)
(push) ; 9
(assert (not (<= 0 k@428)))
(check-sat)
; unknown
(pop) ; 9
; 0.01s
; (get-info :all-statistics)
(push) ; 9
; [then-branch 83] 0 <= k@428
(assert (<= 0 k@428))
; [eval] k < x.Set__max
(pop) ; 9
(push) ; 9
; [else-branch 83] !0 <= k@428
(assert (not (<= 0 k@428)))
(pop) ; 9
(pop) ; 8
(assert (and (<= 0 k@428) (< k@428 $t@414)))
; [eval] x.Set__contents[k]
(set-option :timeout 0)
(push) ; 8
(assert (not (not (= $k@427 $Perm.No))))
(check-sat)
; unsat
(pop) ; 8
; 0.00s
; (get-info :all-statistics)
(assert (not (= $k@427 $Perm.No)))
(declare-const $k@429 $Perm)
(assert ($Perm.isValidVar $k@429))
(assert ($Perm.isReadVar $k@429 $Perm.Write))
(pop) ; 7
(assert (not (= $k@427 $Perm.No)))
(assert ($Perm.isValidVar $k@429))
(assert ($Perm.isReadVar $k@429 $Perm.Write))
(declare-fun invOf@430 ($Ref) Int)
(assert (forall (($r $Ref)) (!
  (implies
    (and (<= 0 (invOf@430 $r)) (< (invOf@430 $r) $t@414))
    (= ($Seq.index $t@411 (invOf@430 $r)) $r))
  :pattern ((invOf@430 $r)))))
(assert (forall ((k@428 Int)) (!
  (implies
    (and (<= 0 k@428) (< k@428 $t@414))
    (= (invOf@430 ($Seq.index $t@411 k@428)) k@428))
  :pattern (($Seq.index $t@411 k@428)))))
(assert (forall ((k@428 Int)) (!
  (iff
    ($Set.in ($Seq.index $t@411 k@428) ($FVF.domain_Ref__Boolean_value $t@407))
    (and (<= 0 k@428) (< k@428 $t@414)))
  :pattern (($Set.in
    ($Seq.index $t@411 k@428)
    ($FVF.domain_Ref__Boolean_value $t@407))))))
(assert (forall ((k@428 Int)) (!
  (implies
    (and (and (<= 0 k@428) (< k@428 $t@414)) (< $Perm.No $k@429))
    (not (= ($Seq.index $t@411 k@428) $Ref.null)))
  :pattern (($Seq.index $t@411 k@428)))))
(assert (< $Perm.No $k@429))
; [eval] (forall k: Int :: (k >= x.Set__max) && (k < j) ==> !diz.Set__contents[k].Ref__Boolean_value)
(declare-const k@431 Int)
(push) ; 7
; [eval] (k >= x.Set__max) && (k < j) ==> !diz.Set__contents[k].Ref__Boolean_value
; [eval] (k >= x.Set__max) && (k < j)
; [eval] k >= x.Set__max
(push) ; 8
(set-option :timeout 0)
(push) ; 9
(assert (not (not (>= k@431 $t@414))))
(check-sat)
; unknown
(pop) ; 9
; 0.01s
; (get-info :all-statistics)
(set-option :timeout 0)
(push) ; 9
(assert (not (>= k@431 $t@414)))
(check-sat)
; unknown
(pop) ; 9
; 0.01s
; (get-info :all-statistics)
(push) ; 9
; [then-branch 84] k@431 >= $t@414
(assert (>= k@431 $t@414))
; [eval] k < j
(pop) ; 9
(push) ; 9
; [else-branch 84] !k@431 >= $t@414
(assert (not (>= k@431 $t@414)))
(pop) ; 9
(pop) ; 8
(push) ; 8
(set-option :timeout 0)
(push) ; 9
(assert (not (not (and (>= k@431 $t@414) (< k@431 j@400)))))
(check-sat)
; unknown
(pop) ; 9
; 0.01s
; (get-info :all-statistics)
(set-option :timeout 0)
(push) ; 9
(assert (not (and (>= k@431 $t@414) (< k@431 j@400))))
(check-sat)
; unknown
(pop) ; 9
; 0.01s
; (get-info :all-statistics)
(push) ; 9
; [then-branch 85] k@431 >= $t@414 && k@431 < j@400
(assert (and (>= k@431 $t@414) (< k@431 j@400)))
; [eval] !diz.Set__contents[k].Ref__Boolean_value
; [eval] diz.Set__contents[k]
(set-option :timeout 0)
(push) ; 10
(assert (not (not (= ($Seq.index $t@420 k@431) $Ref.null))))
(check-sat)
; unsat
(pop) ; 10
; 0.00s
; (get-info :all-statistics)
(set-option :timeout 0)
(push) ; 10
(assert (not (<
  $Perm.No
  (+
    (ite
      (and
        (<= 0 (invOf@425 ($Seq.index $t@420 k@431)))
        (< (invOf@425 ($Seq.index $t@420 k@431)) $t@421))
      $Perm.Write
      $Perm.No)
    (ite
      (and
        (<= 0 (invOf@430 ($Seq.index $t@420 k@431)))
        (< (invOf@430 ($Seq.index $t@420 k@431)) $t@414))
      $k@429
      $Perm.No)))))
(check-sat)
; unsat
(pop) ; 10
; 0.00s
; (get-info :all-statistics)
(declare-const fvf@432 $FVF<Bool>)
(assert (forall (($r $Ref)) (!
  (implies
    (and
      (and (<= 0 (invOf@425 $r)) (< (invOf@425 $r) $t@421))
      ($Set.in $r ($FVF.domain_Ref__Boolean_value fvf@432)))
    (=
      ($FVF.lookup_Ref__Boolean_value fvf@432 $r)
      ($FVF.lookup_Ref__Boolean_value $t@417 $r)))
  :pattern (($FVF.lookup_Ref__Boolean_value fvf@432 $r) (invOf@425 $r))
  :pattern (($FVF.lookup_Ref__Boolean_value $t@417 $r) (invOf@425 $r)))))
(assert (forall (($r $Ref)) (!
  (implies
    (and
      (ite
        (and (<= 0 (invOf@430 $r)) (< (invOf@430 $r) $t@414))
        (< $Perm.No $k@429)
        false)
      ($Set.in $r ($FVF.domain_Ref__Boolean_value fvf@432)))
    (=
      ($FVF.lookup_Ref__Boolean_value fvf@432 $r)
      ($FVF.lookup_Ref__Boolean_value $t@407 $r)))
  :pattern (($FVF.lookup_Ref__Boolean_value fvf@432 $r) (invOf@430 $r))
  :pattern (($FVF.lookup_Ref__Boolean_value $t@407 $r) (invOf@430 $r)))))
(assert (forall ((k@431 Int)) (!
  (iff
    ($Set.in ($Seq.index $t@420 k@431) ($FVF.domain_Ref__Boolean_value fvf@432))
    (and (and (>= k@431 $t@414) (< k@431 j@400)) (not (<= $t@116 $t@123))))
  :pattern (($Set.in
    ($Seq.index $t@420 k@431)
    ($FVF.domain_Ref__Boolean_value fvf@432))))))
(pop) ; 9
(push) ; 9
; [else-branch 85] !k@431 >= $t@414 && k@431 < j@400
(assert (not (and (>= k@431 $t@414) (< k@431 j@400))))
(pop) ; 9
(pop) ; 8
(assert (forall ((k@431 Int)) (!
  (iff
    ($Set.in ($Seq.index $t@420 k@431) ($FVF.domain_Ref__Boolean_value fvf@432))
    (and (and (>= k@431 $t@414) (< k@431 j@400)) (not (<= $t@116 $t@123))))
  :pattern (($Set.in
    ($Seq.index $t@420 k@431)
    ($FVF.domain_Ref__Boolean_value fvf@432))))))
(assert (forall (($r $Ref)) (!
  (implies
    (and
      (ite
        (and (<= 0 (invOf@430 $r)) (< (invOf@430 $r) $t@414))
        (< $Perm.No $k@429)
        false)
      ($Set.in $r ($FVF.domain_Ref__Boolean_value fvf@432)))
    (=
      ($FVF.lookup_Ref__Boolean_value fvf@432 $r)
      ($FVF.lookup_Ref__Boolean_value $t@407 $r)))
  :pattern (($FVF.lookup_Ref__Boolean_value fvf@432 $r) (invOf@430 $r))
  :pattern (($FVF.lookup_Ref__Boolean_value $t@407 $r) (invOf@430 $r)))))
(assert (forall (($r $Ref)) (!
  (implies
    (and
      (and (<= 0 (invOf@425 $r)) (< (invOf@425 $r) $t@421))
      ($Set.in $r ($FVF.domain_Ref__Boolean_value fvf@432)))
    (=
      ($FVF.lookup_Ref__Boolean_value fvf@432 $r)
      ($FVF.lookup_Ref__Boolean_value $t@417 $r)))
  :pattern (($FVF.lookup_Ref__Boolean_value fvf@432 $r) (invOf@425 $r))
  :pattern (($FVF.lookup_Ref__Boolean_value $t@417 $r) (invOf@425 $r)))))
(pop) ; 7
(assert (forall ((k@431 Int)) (!
  (iff
    ($Set.in ($Seq.index $t@420 k@431) ($FVF.domain_Ref__Boolean_value fvf@432))
    (and (and (>= k@431 $t@414) (< k@431 j@400)) (not (<= $t@116 $t@123))))
  :pattern (($Set.in
    ($Seq.index $t@420 k@431)
    ($FVF.domain_Ref__Boolean_value fvf@432))))))
(assert (forall (($r $Ref)) (!
  (implies
    (and
      (ite
        (and (<= 0 (invOf@430 $r)) (< (invOf@430 $r) $t@414))
        (< $Perm.No $k@429)
        false)
      ($Set.in $r ($FVF.domain_Ref__Boolean_value fvf@432)))
    (=
      ($FVF.lookup_Ref__Boolean_value fvf@432 $r)
      ($FVF.lookup_Ref__Boolean_value $t@407 $r)))
  :pattern (($FVF.lookup_Ref__Boolean_value fvf@432 $r) (invOf@430 $r))
  :pattern (($FVF.lookup_Ref__Boolean_value $t@407 $r) (invOf@430 $r)))))
(assert (forall (($r $Ref)) (!
  (implies
    (and
      (and (<= 0 (invOf@425 $r)) (< (invOf@425 $r) $t@421))
      ($Set.in $r ($FVF.domain_Ref__Boolean_value fvf@432)))
    (=
      ($FVF.lookup_Ref__Boolean_value fvf@432 $r)
      ($FVF.lookup_Ref__Boolean_value $t@417 $r)))
  :pattern (($FVF.lookup_Ref__Boolean_value fvf@432 $r) (invOf@425 $r))
  :pattern (($FVF.lookup_Ref__Boolean_value $t@417 $r) (invOf@425 $r)))))
(assert (forall ((k@431 Int)) (!
  (implies
    (and (>= k@431 $t@414) (< k@431 j@400))
    (not ($FVF.lookup_Ref__Boolean_value fvf@432 ($Seq.index $t@420 k@431))))
  :pattern (($Seq.index $t@420 k@431)))))
; [eval] j < diz.Set__max
(assert (< j@400 $t@421))
(set-option :timeout 0)
(check-sat)
; unknown
; [exec]
; __flatten_16 := diz.Set__contents[j]
; [eval] diz.Set__contents[j]
; [exec]
; __flatten_17 := false
; [exec]
; __flatten_16.Ref__Boolean_value := __flatten_17
(set-option :timeout 0)
(push) ; 7
(assert (not (not (= ($Seq.index $t@420 j@400) $Ref.null))))
(check-sat)
; unsat
(pop) ; 7
; 0.00s
; (get-info :all-statistics)
(declare-const fvf@433 $FVF<Bool>)
; Precomputing split data for $t@420[j@400].Ref__Boolean_value # W
(define-fun $permsTaken35 (($r $Ref)) $Perm
  ($Perm.min
    (ite (= $r ($Seq.index $t@420 j@400)) $Perm.Write $Perm.No)
    (ite
      (= $r ($Seq.index $t@420 j@400))
      (ite
        (and (<= 0 (invOf@425 $r)) (< (invOf@425 $r) $t@421))
        $Perm.Write
        $Perm.No)
      $Perm.No)))
(define-fun $permsTaken36 (($r $Ref)) $Perm
  ($Perm.min
    (-
      (ite (= $r ($Seq.index $t@420 j@400)) $Perm.Write $Perm.No)
      ($permsTaken35 $r))
    (ite
      (= $r ($Seq.index $t@420 j@400))
      (ite (and (<= 0 (invOf@430 $r)) (< (invOf@430 $r) $t@414)) $k@429 $Perm.No)
      $Perm.No)))
; Done precomputing, updating quantified heap chunks
; Chunk depleted?
(set-option :timeout 500)
(push) ; 7
(assert (not (forall (($r $Ref)) (!
  (=
    (-
      (ite
        (and (<= 0 (invOf@425 $r)) (< (invOf@425 $r) $t@421))
        $Perm.Write
        $Perm.No)
      ($permsTaken35 $r))
    $Perm.No)
  ))))
(check-sat)
; unknown
(pop) ; 7
; 0.11s
; (get-info :all-statistics)
; Enough permissions taken?
(set-option :timeout 500)
(push) ; 7
(assert (not (= (- $Perm.Write ($permsTaken35 ($Seq.index $t@420 j@400))) $Perm.No)))
(check-sat)
; unsat
(pop) ; 7
; 0.00s
; (get-info :all-statistics)
; Final check that enough permissions have been taken
; Done splitting
(declare-const fvf@434 $FVF<Bool>)
(assert (= ($FVF.lookup_Ref__Boolean_value fvf@434 ($Seq.index $t@420 j@400)) false))
(assert ($Set.equal
  ($FVF.domain_Ref__Boolean_value fvf@434)
  ($Set.singleton  ($Seq.index $t@420 j@400))))
; [exec]
; j := j + 1
; [eval] j + 1
(declare-const $k@435 $Perm)
(assert ($Perm.isValidVar $k@435))
(assert ($Perm.isReadVar $k@435 $Perm.Write))
(set-option :timeout 0)
(push) ; 7
(assert (not (or (= $k@435 $Perm.No) true)))
(check-sat)
; unsat
(pop) ; 7
; 0.00s
; (get-info :all-statistics)
(assert (< $k@435 $k@422))
; [eval] diz.Set__max > 0
(declare-const $k@436 $Perm)
(assert ($Perm.isValidVar $k@436))
(assert ($Perm.isReadVar $k@436 $Perm.Write))
(set-option :timeout 0)
(push) ; 7
(assert (not (or (= $k@436 $Perm.No) true)))
(check-sat)
; unsat
(pop) ; 7
; 0.00s
; (get-info :all-statistics)
(assert (< $k@436 $k@423))
; [eval] |diz.Set__contents| == diz.Set__max
; [eval] |diz.Set__contents|
(declare-const fvf@437 $FVF<Int>)
(declare-const fvf@438 $FVF<Int>)
(declare-const fvf@439 $FVF<$Seq<$Ref>>)
(declare-const fvf@440 $FVF<$Seq<$Ref>>)
(assert (= ($FVF.lookup_Set__max fvf@437 x@102) $t@414))
(assert ($Set.equal ($FVF.domain_Set__max fvf@437) ($Set.singleton  x@102)))
(assert (= ($FVF.lookup_Set__max fvf@438 diz@101) $t@421))
(assert ($Set.equal ($FVF.domain_Set__max fvf@438) ($Set.singleton  diz@101)))
(assert ($Seq.equal ($FVF.lookup_Set__contents fvf@439 x@102) $t@411))
(assert ($Set.equal ($FVF.domain_Set__contents fvf@439) ($Set.singleton  x@102)))
(assert ($Seq.equal ($FVF.lookup_Set__contents fvf@440 diz@101) $t@420))
(assert ($Set.equal ($FVF.domain_Set__contents fvf@440) ($Set.singleton  diz@101)))
(declare-const k@441 Int)
; [eval] (0 <= k) && (k < diz.Set__max)
; [eval] 0 <= k
(push) ; 7
(set-option :timeout 0)
(push) ; 8
(assert (not (not (<= 0 k@441))))
(check-sat)
; unknown
(pop) ; 8
; 0.02s
; (get-info :all-statistics)
(set-option :timeout 0)
(push) ; 8
(assert (not (<= 0 k@441)))
(check-sat)
; unknown
(pop) ; 8
; 0.02s
; (get-info :all-statistics)
(push) ; 8
; [then-branch 86] 0 <= k@441
(assert (<= 0 k@441))
; [eval] k < diz.Set__max
(set-option :timeout 0)
(push) ; 9
(assert (not (< $Perm.No (+ (ite (= diz@101 x@102) $k@426 $Perm.No) $k@422))))
(check-sat)
; unsat
(pop) ; 9
; 0.00s
; (get-info :all-statistics)
(declare-const fvf@442 $FVF<Int>)
(assert (implies
  (ite (= diz@101 x@102) (< $Perm.No $k@426) false)
  (=
    ($FVF.lookup_Set__max fvf@442 diz@101)
    ($FVF.lookup_Set__max fvf@437 diz@101))))
(assert (implies
  (< $Perm.No $k@422)
  (=
    ($FVF.lookup_Set__max fvf@442 diz@101)
    ($FVF.lookup_Set__max fvf@438 diz@101))))
(assert ($Set.equal ($FVF.domain_Set__max fvf@442) ($Set.singleton  diz@101)))
(pop) ; 8
(push) ; 8
; [else-branch 86] !0 <= k@441
(assert (not (<= 0 k@441)))
(pop) ; 8
(pop) ; 7
(assert ($Set.equal ($FVF.domain_Set__max fvf@442) ($Set.singleton  diz@101)))
(assert (implies
  (< $Perm.No $k@422)
  (=
    ($FVF.lookup_Set__max fvf@442 diz@101)
    ($FVF.lookup_Set__max fvf@438 diz@101))))
(assert (implies
  (ite (= diz@101 x@102) (< $Perm.No $k@426) false)
  (=
    ($FVF.lookup_Set__max fvf@442 diz@101)
    ($FVF.lookup_Set__max fvf@437 diz@101))))
(set-option :timeout 0)
(push) ; 7
(assert (not (not (and (<= 0 k@441) (< k@441 ($FVF.lookup_Set__max fvf@442 diz@101))))))
(check-sat)
; unknown
(pop) ; 7
; 0.01s
; (get-info :all-statistics)
(assert (and (<= 0 k@441) (< k@441 ($FVF.lookup_Set__max fvf@442 diz@101))))
; [eval] diz.Set__contents[k]
(set-option :timeout 0)
(push) ; 7
(assert (not (< $Perm.No (+ (ite (= diz@101 x@102) $k@427 $Perm.No) $k@423))))
(check-sat)
; unsat
(pop) ; 7
; 0.00s
; (get-info :all-statistics)
(declare-const fvf@443 $FVF<$Seq<$Ref>>)
(assert (implies
  (ite (= diz@101 x@102) (< $Perm.No $k@427) false)
  ($Seq.equal
    ($FVF.lookup_Set__contents fvf@443 diz@101)
    ($FVF.lookup_Set__contents fvf@439 diz@101))))
(assert (implies
  (< $Perm.No $k@423)
  ($Seq.equal
    ($FVF.lookup_Set__contents fvf@443 diz@101)
    ($FVF.lookup_Set__contents fvf@440 diz@101))))
(assert ($Set.equal ($FVF.domain_Set__contents fvf@443) ($Set.singleton  diz@101)))
(set-option :timeout 0)
(push) ; 7
(assert (not (forall (($x Int) ($y Int)) (!
  (implies
    (and
      (and (<= 0 $x) (< $x ($FVF.lookup_Set__max fvf@442 diz@101)))
      (and (<= 0 $y) (< $y ($FVF.lookup_Set__max fvf@442 diz@101)))
      (=
        ($Seq.index ($FVF.lookup_Set__contents fvf@443 diz@101) $x)
        ($Seq.index ($FVF.lookup_Set__contents fvf@443 diz@101) $y)))
    (= $x $y))
  :pattern (($Seq.index ($FVF.lookup_Set__contents fvf@443 diz@101) $x) ($Seq.index
    ($FVF.lookup_Set__contents fvf@443 diz@101)
    $y))))))
(check-sat)
; unsat
(pop) ; 7
; 0.00s
; (get-info :all-statistics)
(declare-fun invOf@444 ($Ref) Int)
(assert (forall (($r $Ref)) (!
  (implies
    (and
      (<= 0 (invOf@444 $r))
      (< (invOf@444 $r) ($FVF.lookup_Set__max fvf@442 diz@101)))
    (=
      ($Seq.index ($FVF.lookup_Set__contents fvf@443 diz@101) (invOf@444 $r))
      $r))
  :pattern ((invOf@444 $r)))))
(assert (forall ((k@441 Int)) (!
  (implies
    (and (<= 0 k@441) (< k@441 ($FVF.lookup_Set__max fvf@442 diz@101)))
    (=
      (invOf@444 ($Seq.index ($FVF.lookup_Set__contents fvf@443 diz@101) k@441))
      k@441))
  :pattern (($Seq.index ($FVF.lookup_Set__contents fvf@443 diz@101) k@441)))))
(declare-const fvf@445 $FVF<Bool>)
; Precomputing split data for Lookup(Set__contents,fvf@443,diz@101)[k@441].Ref__Boolean_value # W
(define-fun $permsTaken37 (($r $Ref)) $Perm
  ($Perm.min
    (ite
      (and
        (<= 0 (invOf@444 $r))
        (< (invOf@444 $r) ($FVF.lookup_Set__max fvf@442 diz@101)))
      $Perm.Write
      $Perm.No)
    (ite
      (= $r ($Seq.index ($FVF.lookup_Set__contents fvf@443 diz@101) k@441))
      (ite (= $r ($Seq.index $t@420 j@400)) $Perm.Write $Perm.No)
      $Perm.No)))
(define-fun $permsTaken38 (($r $Ref)) $Perm
  ($Perm.min
    (-
      (ite
        (and
          (<= 0 (invOf@444 $r))
          (< (invOf@444 $r) ($FVF.lookup_Set__max fvf@442 diz@101)))
        $Perm.Write
        $Perm.No)
      ($permsTaken37 $r))
    (ite
      (= $r ($Seq.index ($FVF.lookup_Set__contents fvf@443 diz@101) k@441))
      (-
        (ite
          (and (<= 0 (invOf@425 $r)) (< (invOf@425 $r) $t@421))
          $Perm.Write
          $Perm.No)
        ($permsTaken35 $r))
      $Perm.No)))
(define-fun $permsTaken39 (($r $Ref)) $Perm
  ($Perm.min
    (-
      (-
        (ite
          (and
            (<= 0 (invOf@444 $r))
            (< (invOf@444 $r) ($FVF.lookup_Set__max fvf@442 diz@101)))
          $Perm.Write
          $Perm.No)
        ($permsTaken37 $r))
      ($permsTaken38 $r))
    (ite
      (= $r ($Seq.index ($FVF.lookup_Set__contents fvf@443 diz@101) k@441))
      (ite (and (<= 0 (invOf@430 $r)) (< (invOf@430 $r) $t@414)) $k@429 $Perm.No)
      $Perm.No)))
; Done precomputing, updating quantified heap chunks
; Chunk depleted?
(set-option :timeout 500)
(push) ; 7
(assert (not (forall (($r $Ref)) (!
  (=
    (-
      (ite (= $r ($Seq.index $t@420 j@400)) $Perm.Write $Perm.No)
      ($permsTaken37 $r))
    $Perm.No)
  ))))
(check-sat)
; unknown
(pop) ; 7
; 0.10s
; (get-info :all-statistics)
; Enough permissions taken?
(set-option :timeout 500)
(push) ; 7
(assert (not (=
  (-
    (ite
      (and
        (<=
          0
          (invOf@444 ($Seq.index
            ($FVF.lookup_Set__contents fvf@443 diz@101)
            k@441)))
        (<
          (invOf@444 ($Seq.index
            ($FVF.lookup_Set__contents fvf@443 diz@101)
            k@441))
          ($FVF.lookup_Set__max fvf@442 diz@101)))
      $Perm.Write
      $Perm.No)
    ($permsTaken37 ($Seq.index ($FVF.lookup_Set__contents fvf@443 diz@101) k@441)))
  $Perm.No)))
(check-sat)
; unknown
(pop) ; 7
; 0.09s
; (get-info :all-statistics)
; Chunk depleted?
(set-option :timeout 500)
(push) ; 7
(assert (not (forall (($r $Ref)) (!
  (=
    (-
      (-
        (ite
          (and (<= 0 (invOf@425 $r)) (< (invOf@425 $r) $t@421))
          $Perm.Write
          $Perm.No)
        ($permsTaken35 $r))
      ($permsTaken38 $r))
    $Perm.No)
  ))))
(check-sat)
; unknown
(pop) ; 7
; 0.10s
; (get-info :all-statistics)
; Enough permissions taken?
(set-option :timeout 500)
(push) ; 7
(assert (not (=
  (-
    (-
      (ite
        (and
          (<=
            0
            (invOf@444 ($Seq.index
              ($FVF.lookup_Set__contents fvf@443 diz@101)
              k@441)))
          (<
            (invOf@444 ($Seq.index
              ($FVF.lookup_Set__contents fvf@443 diz@101)
              k@441))
            ($FVF.lookup_Set__max fvf@442 diz@101)))
        $Perm.Write
        $Perm.No)
      ($permsTaken37 ($Seq.index
        ($FVF.lookup_Set__contents fvf@443 diz@101)
        k@441)))
    ($permsTaken38 ($Seq.index ($FVF.lookup_Set__contents fvf@443 diz@101) k@441)))
  $Perm.No)))
(check-sat)
; unsat
(pop) ; 7
; 0.00s
; (get-info :all-statistics)
; Final check that enough permissions have been taken
; Done splitting
(assert (forall (($r $Ref)) (!
  (implies
    (and
      (ite
        (and (<= 0 (invOf@430 $r)) (< (invOf@430 $r) $t@414))
        (< $Perm.No $k@429)
        false)
      ($Set.in $r ($FVF.domain_Ref__Boolean_value fvf@445)))
    (=
      ($FVF.lookup_Ref__Boolean_value fvf@445 $r)
      ($FVF.lookup_Ref__Boolean_value $t@407 $r)))
  :pattern (($FVF.lookup_Ref__Boolean_value fvf@445 $r) (invOf@430 $r))
  :pattern (($FVF.lookup_Ref__Boolean_value $t@407 $r) (invOf@430 $r)))))
(assert (forall (($r $Ref)) (!
  (implies
    (and
      (<
        $Perm.No
        (-
          (ite
            (and (<= 0 (invOf@425 $r)) (< (invOf@425 $r) $t@421))
            $Perm.Write
            $Perm.No)
          ($permsTaken35 $r)))
      ($Set.in $r ($FVF.domain_Ref__Boolean_value fvf@445)))
    (=
      ($FVF.lookup_Ref__Boolean_value fvf@445 $r)
      ($FVF.lookup_Ref__Boolean_value $t@417 $r)))
  :pattern (($FVF.lookup_Ref__Boolean_value fvf@445 $r) (invOf@425 $r))
  :pattern (($FVF.lookup_Ref__Boolean_value $t@417 $r) (invOf@425 $r)))))
(assert (forall (($r $Ref)) (!
  (implies
    (and
      (= $r ($Seq.index $t@420 j@400))
      ($Set.in $r ($FVF.domain_Ref__Boolean_value fvf@445)))
    (=
      ($FVF.lookup_Ref__Boolean_value fvf@445 $r)
      ($FVF.lookup_Ref__Boolean_value fvf@434 $r)))
  :pattern (($FVF.lookup_Ref__Boolean_value fvf@445 $r))
  :pattern (($FVF.lookup_Ref__Boolean_value fvf@434 $r)))))
(assert (forall (($r $Ref)) (!
  (iff
    ($Set.in $r ($FVF.domain_Ref__Boolean_value fvf@445))
    (and
      (<= 0 (invOf@444 $r))
      (< (invOf@444 $r) ($FVF.lookup_Set__max fvf@442 diz@101))))
  :pattern (($Set.in $r ($FVF.domain_Ref__Boolean_value fvf@445))))))
; [eval] x != null
(declare-const $k@446 $Perm)
(assert ($Perm.isValidVar $k@446))
(assert ($Perm.isReadVar $k@446 $Perm.Write))
(set-option :timeout 0)
(push) ; 7
(assert (not (or (= $k@446 $Perm.No) true)))
(check-sat)
; unsat
(pop) ; 7
; 0.00s
; (get-info :all-statistics)
(assert (< $k@446 $k@426))
; [eval] x.Set__max > 0
(declare-const $k@447 $Perm)
(assert ($Perm.isValidVar $k@447))
(assert ($Perm.isReadVar $k@447 $Perm.Write))
(set-option :timeout 0)
(push) ; 7
(assert (not (or (= $k@447 $Perm.No) true)))
(check-sat)
; unsat
(pop) ; 7
; 0.00s
; (get-info :all-statistics)
(assert (< $k@447 $k@427))
; [eval] diz.Set__max > x.Set__max
; [eval] (j >= x.Set__max) && (j <= diz.Set__max)
; [eval] j >= x.Set__max
(push) ; 7
(set-option :timeout 0)
(push) ; 8
(assert (not (not (>= (+ j@400 1) $t@414))))
(check-sat)
; unknown
(pop) ; 8
; 0.02s
; (get-info :all-statistics)
(set-option :timeout 0)
(push) ; 8
(assert (not (>= (+ j@400 1) $t@414)))
(check-sat)
; unsat
(pop) ; 8
; 0.00s
; (get-info :all-statistics)
(push) ; 8
; [then-branch 87] j@400 + 1 >= $t@414
(assert (>= (+ j@400 1) $t@414))
; [eval] j <= diz.Set__max
(pop) ; 8
; [dead else-branch 87] !j@400 + 1 >= $t@414
(pop) ; 7
(set-option :timeout 0)
(push) ; 7
(assert (not (and (>= (+ j@400 1) $t@414) (<= (+ j@400 1) $t@421))))
(check-sat)
; unsat
(pop) ; 7
; 0.00s
; (get-info :all-statistics)
(assert (and (>= (+ j@400 1) $t@414) (<= (+ j@400 1) $t@421)))
(declare-const fvf@448 $FVF<Int>)
(declare-const fvf@449 $FVF<Int>)
(declare-const fvf@450 $FVF<$Seq<$Ref>>)
(declare-const fvf@451 $FVF<$Seq<$Ref>>)
(assert (= ($FVF.lookup_Set__max fvf@448 x@102) $t@414))
(assert ($Set.equal ($FVF.domain_Set__max fvf@448) ($Set.singleton  x@102)))
(assert (= ($FVF.lookup_Set__max fvf@449 diz@101) $t@421))
(assert ($Set.equal ($FVF.domain_Set__max fvf@449) ($Set.singleton  diz@101)))
(assert ($Seq.equal ($FVF.lookup_Set__contents fvf@450 x@102) $t@411))
(assert ($Set.equal ($FVF.domain_Set__contents fvf@450) ($Set.singleton  x@102)))
(assert ($Seq.equal ($FVF.lookup_Set__contents fvf@451 diz@101) $t@420))
(assert ($Set.equal ($FVF.domain_Set__contents fvf@451) ($Set.singleton  diz@101)))
(declare-const k@452 Int)
; [eval] (0 <= k) && (k < x.Set__max)
; [eval] 0 <= k
(push) ; 7
(set-option :timeout 0)
(push) ; 8
(assert (not (not (<= 0 k@452))))
(check-sat)
; unknown
(pop) ; 8
; 0.02s
; (get-info :all-statistics)
(set-option :timeout 0)
(push) ; 8
(assert (not (<= 0 k@452)))
(check-sat)
; unknown
(pop) ; 8
; 0.02s
; (get-info :all-statistics)
(push) ; 8
; [then-branch 88] 0 <= k@452
(assert (<= 0 k@452))
; [eval] k < x.Set__max
(set-option :timeout 0)
(push) ; 9
(assert (not (< $Perm.No (+ $k@426 (ite (= x@102 diz@101) $k@422 $Perm.No)))))
(check-sat)
; unsat
(pop) ; 9
; 0.00s
; (get-info :all-statistics)
(declare-const fvf@453 $FVF<Int>)
(assert (implies
  (< $Perm.No $k@426)
  (= ($FVF.lookup_Set__max fvf@453 x@102) ($FVF.lookup_Set__max fvf@448 x@102))))
(assert (implies
  (ite (= x@102 diz@101) (< $Perm.No $k@422) false)
  (= ($FVF.lookup_Set__max fvf@453 x@102) ($FVF.lookup_Set__max fvf@449 x@102))))
(assert ($Set.equal ($FVF.domain_Set__max fvf@453) ($Set.singleton  x@102)))
(pop) ; 8
(push) ; 8
; [else-branch 88] !0 <= k@452
(assert (not (<= 0 k@452)))
(pop) ; 8
(pop) ; 7
(assert ($Set.equal ($FVF.domain_Set__max fvf@453) ($Set.singleton  x@102)))
(assert (implies
  (ite (= x@102 diz@101) (< $Perm.No $k@422) false)
  (= ($FVF.lookup_Set__max fvf@453 x@102) ($FVF.lookup_Set__max fvf@449 x@102))))
(assert (implies
  (< $Perm.No $k@426)
  (= ($FVF.lookup_Set__max fvf@453 x@102) ($FVF.lookup_Set__max fvf@448 x@102))))
(set-option :timeout 0)
(push) ; 7
(assert (not (not (and (<= 0 k@452) (< k@452 ($FVF.lookup_Set__max fvf@453 x@102))))))
(check-sat)
; unknown
(pop) ; 7
; 0.02s
; (get-info :all-statistics)
(assert (and (<= 0 k@452) (< k@452 ($FVF.lookup_Set__max fvf@453 x@102))))
(declare-const $k@454 $Perm)
(assert ($Perm.isValidVar $k@454))
(assert ($Perm.isReadVar $k@454 $Perm.Write))
(set-option :timeout 0)
(push) ; 7
(assert (not (or (= $k@454 $Perm.No) true)))
(check-sat)
; unsat
(pop) ; 7
; 0.00s
; (get-info :all-statistics)
; [eval] x.Set__contents[k]
(set-option :timeout 0)
(push) ; 7
(assert (not (< $Perm.No (+ $k@427 (ite (= x@102 diz@101) $k@423 $Perm.No)))))
(check-sat)
; unsat
(pop) ; 7
; 0.00s
; (get-info :all-statistics)
(declare-const fvf@455 $FVF<$Seq<$Ref>>)
(assert (implies
  (< $Perm.No $k@427)
  ($Seq.equal
    ($FVF.lookup_Set__contents fvf@455 x@102)
    ($FVF.lookup_Set__contents fvf@450 x@102))))
(assert (implies
  (ite (= x@102 diz@101) (< $Perm.No $k@423) false)
  ($Seq.equal
    ($FVF.lookup_Set__contents fvf@455 x@102)
    ($FVF.lookup_Set__contents fvf@451 x@102))))
(assert ($Set.equal ($FVF.domain_Set__contents fvf@455) ($Set.singleton  x@102)))
(set-option :timeout 0)
(push) ; 7
(assert (not (forall (($x Int) ($y Int)) (!
  (implies
    (and
      (and (<= 0 $x) (< $x ($FVF.lookup_Set__max fvf@453 x@102)))
      (and (<= 0 $y) (< $y ($FVF.lookup_Set__max fvf@453 x@102)))
      (=
        ($Seq.index ($FVF.lookup_Set__contents fvf@455 x@102) $x)
        ($Seq.index ($FVF.lookup_Set__contents fvf@455 x@102) $y)))
    (= $x $y))
  :pattern (($Seq.index ($FVF.lookup_Set__contents fvf@455 x@102) $x) ($Seq.index
    ($FVF.lookup_Set__contents fvf@455 x@102)
    $y))))))
(check-sat)
; unsat
(pop) ; 7
; 0.00s
; (get-info :all-statistics)
(declare-fun invOf@456 ($Ref) Int)
(assert (forall (($r $Ref)) (!
  (implies
    (and
      (<= 0 (invOf@456 $r))
      (< (invOf@456 $r) ($FVF.lookup_Set__max fvf@453 x@102)))
    (= ($Seq.index ($FVF.lookup_Set__contents fvf@455 x@102) (invOf@456 $r)) $r))
  :pattern ((invOf@456 $r)))))
(assert (forall ((k@452 Int)) (!
  (implies
    (and (<= 0 k@452) (< k@452 ($FVF.lookup_Set__max fvf@453 x@102)))
    (=
      (invOf@456 ($Seq.index ($FVF.lookup_Set__contents fvf@455 x@102) k@452))
      k@452))
  :pattern (($Seq.index ($FVF.lookup_Set__contents fvf@455 x@102) k@452)))))
(declare-const fvf@457 $FVF<Bool>)
; Precomputing split data for Lookup(Set__contents,fvf@455,x@102)[k@452].Ref__Boolean_value # $k@454
(define-fun $permsTaken40 (($r $Ref)) $Perm
  ($Perm.min
    (ite
      (and
        (<= 0 (invOf@456 $r))
        (< (invOf@456 $r) ($FVF.lookup_Set__max fvf@453 x@102)))
      $k@454
      $Perm.No)
    (ite
      (= $r ($Seq.index ($FVF.lookup_Set__contents fvf@455 x@102) k@452))
      (-
        (ite (= $r ($Seq.index $t@420 j@400)) $Perm.Write $Perm.No)
        ($permsTaken37 $r))
      $Perm.No)))
(define-fun $permsTaken41 (($r $Ref)) $Perm
  ($Perm.min
    (-
      (ite
        (and
          (<= 0 (invOf@456 $r))
          (< (invOf@456 $r) ($FVF.lookup_Set__max fvf@453 x@102)))
        $k@454
        $Perm.No)
      ($permsTaken40 $r))
    (ite
      (= $r ($Seq.index ($FVF.lookup_Set__contents fvf@455 x@102) k@452))
      (-
        (-
          (ite
            (and (<= 0 (invOf@425 $r)) (< (invOf@425 $r) $t@421))
            $Perm.Write
            $Perm.No)
          ($permsTaken35 $r))
        ($permsTaken38 $r))
      $Perm.No)))
(define-fun $permsTaken42 (($r $Ref)) $Perm
  ($Perm.min
    (-
      (-
        (ite
          (and
            (<= 0 (invOf@456 $r))
            (< (invOf@456 $r) ($FVF.lookup_Set__max fvf@453 x@102)))
          $k@454
          $Perm.No)
        ($permsTaken40 $r))
      ($permsTaken41 $r))
    (ite
      (= $r ($Seq.index ($FVF.lookup_Set__contents fvf@455 x@102) k@452))
      (ite (and (<= 0 (invOf@430 $r)) (< (invOf@430 $r) $t@414)) $k@429 $Perm.No)
      $Perm.No)))
; Done precomputing, updating quantified heap chunks
; Constrain original permissions $k@454
(assert (forall (($r $Ref)) (!
  (implies
    (not
      (=
        (-
          (ite (= $r ($Seq.index $t@420 j@400)) $Perm.Write $Perm.No)
          ($permsTaken37 $r))
        $Perm.No))
    (<
      (ite
        (and
          (<= 0 (invOf@456 $r))
          (< (invOf@456 $r) ($FVF.lookup_Set__max fvf@453 x@102)))
        $k@454
        $Perm.No)
      (-
        (ite (= $r ($Seq.index $t@420 j@400)) $Perm.Write $Perm.No)
        ($permsTaken37 $r))))
  :pattern ((invOf@456 $r))
  :pattern ((invOf@456 $r)))))
; Enough permissions taken?
(set-option :timeout 500)
(push) ; 7
(assert (not (=
  (-
    (ite
      (and
        (<=
          0
          (invOf@456 ($Seq.index ($FVF.lookup_Set__contents fvf@455 x@102) k@452)))
        (<
          (invOf@456 ($Seq.index ($FVF.lookup_Set__contents fvf@455 x@102) k@452))
          ($FVF.lookup_Set__max fvf@453 x@102)))
      $k@454
      $Perm.No)
    ($permsTaken40 ($Seq.index ($FVF.lookup_Set__contents fvf@455 x@102) k@452)))
  $Perm.No)))
(check-sat)
; unknown
(pop) ; 7
; 0.17s
; (get-info :all-statistics)
; Constrain original permissions $k@454
(assert (forall (($r $Ref)) (!
  (implies
    (not
      (=
        (-
          (-
            (ite
              (and (<= 0 (invOf@425 $r)) (< (invOf@425 $r) $t@421))
              $Perm.Write
              $Perm.No)
            ($permsTaken35 $r))
          ($permsTaken38 $r))
        $Perm.No))
    (<
      (ite
        (and
          (<= 0 (invOf@456 $r))
          (< (invOf@456 $r) ($FVF.lookup_Set__max fvf@453 x@102)))
        $k@454
        $Perm.No)
      (-
        (-
          (ite
            (and (<= 0 (invOf@425 $r)) (< (invOf@425 $r) $t@421))
            $Perm.Write
            $Perm.No)
          ($permsTaken35 $r))
        ($permsTaken38 $r))))
  :pattern ((invOf@425 $r))
  :pattern ((invOf@425 $r))
  :pattern ((invOf@456 $r))
  :pattern ((invOf@456 $r))
  :pattern ((invOf@425 $r))
  :pattern ((invOf@425 $r)))))
; Enough permissions taken?
(set-option :timeout 500)
(push) ; 7
(assert (not (=
  (-
    (-
      (ite
        (and
          (<=
            0
            (invOf@456 ($Seq.index
              ($FVF.lookup_Set__contents fvf@455 x@102)
              k@452)))
          (<
            (invOf@456 ($Seq.index
              ($FVF.lookup_Set__contents fvf@455 x@102)
              k@452))
            ($FVF.lookup_Set__max fvf@453 x@102)))
        $k@454
        $Perm.No)
      ($permsTaken40 ($Seq.index ($FVF.lookup_Set__contents fvf@455 x@102) k@452)))
    ($permsTaken41 ($Seq.index ($FVF.lookup_Set__contents fvf@455 x@102) k@452)))
  $Perm.No)))
(check-sat)
; unknown
(pop) ; 7
; 0.08s
; (get-info :all-statistics)
; Constrain original permissions $k@454
(assert (forall (($r $Ref)) (!
  (implies
    (not
      (=
        (ite
          (and (<= 0 (invOf@430 $r)) (< (invOf@430 $r) $t@414))
          $k@429
          $Perm.No)
        $Perm.No))
    (ite
      (and (<= 0 (invOf@430 $r)) (< (invOf@430 $r) $t@414))
      (<
        (ite
          (and
            (<= 0 (invOf@456 $r))
            (< (invOf@456 $r) ($FVF.lookup_Set__max fvf@453 x@102)))
          $k@454
          $Perm.No)
        $k@429)
      (<
        (ite
          (and
            (<= 0 (invOf@456 $r))
            (< (invOf@456 $r) ($FVF.lookup_Set__max fvf@453 x@102)))
          $k@454
          $Perm.No)
        $Perm.No)))
  :pattern ((invOf@430 $r))
  :pattern ((invOf@430 $r))
  :pattern ((invOf@430 $r))
  :pattern ((invOf@430 $r))
  :pattern ((invOf@456 $r))
  :pattern ((invOf@456 $r))
  :pattern ((invOf@456 $r))
  :pattern ((invOf@456 $r)))))
; Enough permissions taken?
(set-option :timeout 500)
(push) ; 7
(assert (not (=
  (-
    (-
      (-
        (ite
          (and
            (<=
              0
              (invOf@456 ($Seq.index
                ($FVF.lookup_Set__contents fvf@455 x@102)
                k@452)))
            (<
              (invOf@456 ($Seq.index
                ($FVF.lookup_Set__contents fvf@455 x@102)
                k@452))
              ($FVF.lookup_Set__max fvf@453 x@102)))
          $k@454
          $Perm.No)
        ($permsTaken40 ($Seq.index
          ($FVF.lookup_Set__contents fvf@455 x@102)
          k@452)))
      ($permsTaken41 ($Seq.index ($FVF.lookup_Set__contents fvf@455 x@102) k@452)))
    ($permsTaken42 ($Seq.index ($FVF.lookup_Set__contents fvf@455 x@102) k@452)))
  $Perm.No)))
(check-sat)
; unsat
(pop) ; 7
; 0.02s
; (get-info :all-statistics)
; Final check that enough permissions have been taken
; Done splitting
(assert (forall (($r $Ref)) (!
  (implies
    (and
      (ite
        (and (<= 0 (invOf@430 $r)) (< (invOf@430 $r) $t@414))
        (< $Perm.No $k@429)
        false)
      ($Set.in $r ($FVF.domain_Ref__Boolean_value fvf@457)))
    (=
      ($FVF.lookup_Ref__Boolean_value fvf@457 $r)
      ($FVF.lookup_Ref__Boolean_value $t@407 $r)))
  :pattern (($FVF.lookup_Ref__Boolean_value fvf@457 $r) (invOf@430 $r))
  :pattern (($FVF.lookup_Ref__Boolean_value $t@407 $r) (invOf@430 $r)))))
(assert (forall (($r $Ref)) (!
  (implies
    (and
      (<
        $Perm.No
        (-
          (-
            (ite
              (and (<= 0 (invOf@425 $r)) (< (invOf@425 $r) $t@421))
              $Perm.Write
              $Perm.No)
            ($permsTaken35 $r))
          ($permsTaken38 $r)))
      ($Set.in $r ($FVF.domain_Ref__Boolean_value fvf@457)))
    (=
      ($FVF.lookup_Ref__Boolean_value fvf@457 $r)
      ($FVF.lookup_Ref__Boolean_value $t@417 $r)))
  :pattern (($FVF.lookup_Ref__Boolean_value fvf@457 $r) (invOf@425 $r))
  :pattern (($FVF.lookup_Ref__Boolean_value $t@417 $r) (invOf@425 $r)))))
(assert (forall (($r $Ref)) (!
  (implies
    (and
      (<
        $Perm.No
        (-
          (ite (= $r ($Seq.index $t@420 j@400)) $Perm.Write $Perm.No)
          ($permsTaken37 $r)))
      ($Set.in $r ($FVF.domain_Ref__Boolean_value fvf@457)))
    (=
      ($FVF.lookup_Ref__Boolean_value fvf@457 $r)
      ($FVF.lookup_Ref__Boolean_value fvf@434 $r)))
  :pattern (($FVF.lookup_Ref__Boolean_value fvf@457 $r))
  :pattern (($FVF.lookup_Ref__Boolean_value fvf@434 $r)))))
(assert (forall (($r $Ref)) (!
  (iff
    ($Set.in $r ($FVF.domain_Ref__Boolean_value fvf@457))
    (and
      (<= 0 (invOf@456 $r))
      (< (invOf@456 $r) ($FVF.lookup_Set__max fvf@453 x@102))))
  :pattern (($Set.in $r ($FVF.domain_Ref__Boolean_value fvf@457))))))
; [eval] (forall k: Int :: (k >= x.Set__max) && (k < j) ==> !diz.Set__contents[k].Ref__Boolean_value)
(declare-const k@458 Int)
(push) ; 7
; [eval] (k >= x.Set__max) && (k < j) ==> !diz.Set__contents[k].Ref__Boolean_value
; [eval] (k >= x.Set__max) && (k < j)
; [eval] k >= x.Set__max
(push) ; 8
(set-option :timeout 0)
(push) ; 9
(assert (not (not (>= k@458 $t@414))))
(check-sat)
; unknown
(pop) ; 9
; 0.02s
; (get-info :all-statistics)
(set-option :timeout 0)
(push) ; 9
(assert (not (>= k@458 $t@414)))
(check-sat)
; unknown
(pop) ; 9
; 0.03s
; (get-info :all-statistics)
(push) ; 9
; [then-branch 89] k@458 >= $t@414
(assert (>= k@458 $t@414))
; [eval] k < j
(pop) ; 9
(push) ; 9
; [else-branch 89] !k@458 >= $t@414
(assert (not (>= k@458 $t@414)))
(pop) ; 9
(pop) ; 8
(push) ; 8
(set-option :timeout 0)
(push) ; 9
(assert (not (not (and (>= k@458 $t@414) (< k@458 (+ j@400 1))))))
(check-sat)
; unknown
(pop) ; 9
; 0.02s
; (get-info :all-statistics)
(set-option :timeout 0)
(push) ; 9
(assert (not (and (>= k@458 $t@414) (< k@458 (+ j@400 1)))))
(check-sat)
; unknown
(pop) ; 9
; 0.02s
; (get-info :all-statistics)
(push) ; 9
; [then-branch 90] k@458 >= $t@414 && k@458 < j@400 + 1
(assert (and (>= k@458 $t@414) (< k@458 (+ j@400 1))))
; [eval] !diz.Set__contents[k].Ref__Boolean_value
; [eval] diz.Set__contents[k]
(set-option :timeout 0)
(push) ; 10
(assert (not (not (= ($Seq.index $t@420 k@458) $Ref.null))))
(check-sat)
; unsat
(pop) ; 10
; 0.01s
; (get-info :all-statistics)
(set-option :timeout 0)
(push) ; 10
(assert (not (<
  $Perm.No
  (+
    (+
      (ite
        (and
          (<= 0 (invOf@430 ($Seq.index $t@420 k@458)))
          (< (invOf@430 ($Seq.index $t@420 k@458)) $t@414))
        $k@429
        $Perm.No)
      (-
        (ite
          (and
            (<= 0 (invOf@425 ($Seq.index $t@420 k@458)))
            (< (invOf@425 ($Seq.index $t@420 k@458)) $t@421))
          $Perm.Write
          $Perm.No)
        ($permsTaken35 ($Seq.index $t@420 k@458))))
    (ite
      (= ($Seq.index $t@420 k@458) ($Seq.index $t@420 j@400))
      $Perm.Write
      $Perm.No)))))
(check-sat)
; unsat
(pop) ; 10
; 0.01s
; (get-info :all-statistics)
(declare-const fvf@459 $FVF<Bool>)
(assert (forall (($r $Ref)) (!
  (implies
    (and
      (ite
        (and (<= 0 (invOf@430 $r)) (< (invOf@430 $r) $t@414))
        (< $Perm.No $k@429)
        false)
      ($Set.in $r ($FVF.domain_Ref__Boolean_value fvf@459)))
    (=
      ($FVF.lookup_Ref__Boolean_value fvf@459 $r)
      ($FVF.lookup_Ref__Boolean_value $t@407 $r)))
  :pattern (($FVF.lookup_Ref__Boolean_value fvf@459 $r) (invOf@430 $r))
  :pattern (($FVF.lookup_Ref__Boolean_value $t@407 $r) (invOf@430 $r)))))
(assert (forall (($r $Ref)) (!
  (implies
    (and
      (<
        $Perm.No
        (-
          (ite
            (and (<= 0 (invOf@425 $r)) (< (invOf@425 $r) $t@421))
            $Perm.Write
            $Perm.No)
          ($permsTaken35 $r)))
      ($Set.in $r ($FVF.domain_Ref__Boolean_value fvf@459)))
    (=
      ($FVF.lookup_Ref__Boolean_value fvf@459 $r)
      ($FVF.lookup_Ref__Boolean_value $t@417 $r)))
  :pattern (($FVF.lookup_Ref__Boolean_value fvf@459 $r) (invOf@425 $r))
  :pattern (($FVF.lookup_Ref__Boolean_value $t@417 $r) (invOf@425 $r)))))
(assert (forall (($r $Ref)) (!
  (implies
    (and
      (= $r ($Seq.index $t@420 j@400))
      ($Set.in $r ($FVF.domain_Ref__Boolean_value fvf@459)))
    (=
      ($FVF.lookup_Ref__Boolean_value fvf@459 $r)
      ($FVF.lookup_Ref__Boolean_value fvf@434 $r)))
  :pattern (($FVF.lookup_Ref__Boolean_value fvf@459 $r))
  :pattern (($FVF.lookup_Ref__Boolean_value fvf@434 $r)))))
(assert (forall ((k@458 Int)) (!
  (iff
    ($Set.in ($Seq.index $t@420 k@458) ($FVF.domain_Ref__Boolean_value fvf@459))
    (and (and (>= k@458 $t@414) (< k@458 (+ j@400 1))) (not (<= $t@116 $t@123))))
  :pattern (($Set.in
    ($Seq.index $t@420 k@458)
    ($FVF.domain_Ref__Boolean_value fvf@459))))))
(pop) ; 9
(push) ; 9
; [else-branch 90] !k@458 >= $t@414 && k@458 < j@400 + 1
(assert (not (and (>= k@458 $t@414) (< k@458 (+ j@400 1)))))
(pop) ; 9
(pop) ; 8
(assert (forall ((k@458 Int)) (!
  (iff
    ($Set.in ($Seq.index $t@420 k@458) ($FVF.domain_Ref__Boolean_value fvf@459))
    (and (and (>= k@458 $t@414) (< k@458 (+ j@400 1))) (not (<= $t@116 $t@123))))
  :pattern (($Set.in
    ($Seq.index $t@420 k@458)
    ($FVF.domain_Ref__Boolean_value fvf@459))))))
(assert (forall (($r $Ref)) (!
  (implies
    (and
      (= $r ($Seq.index $t@420 j@400))
      ($Set.in $r ($FVF.domain_Ref__Boolean_value fvf@459)))
    (=
      ($FVF.lookup_Ref__Boolean_value fvf@459 $r)
      ($FVF.lookup_Ref__Boolean_value fvf@434 $r)))
  :pattern (($FVF.lookup_Ref__Boolean_value fvf@459 $r))
  :pattern (($FVF.lookup_Ref__Boolean_value fvf@434 $r)))))
(assert (forall (($r $Ref)) (!
  (implies
    (and
      (<
        $Perm.No
        (-
          (ite
            (and (<= 0 (invOf@425 $r)) (< (invOf@425 $r) $t@421))
            $Perm.Write
            $Perm.No)
          ($permsTaken35 $r)))
      ($Set.in $r ($FVF.domain_Ref__Boolean_value fvf@459)))
    (=
      ($FVF.lookup_Ref__Boolean_value fvf@459 $r)
      ($FVF.lookup_Ref__Boolean_value $t@417 $r)))
  :pattern (($FVF.lookup_Ref__Boolean_value fvf@459 $r) (invOf@425 $r))
  :pattern (($FVF.lookup_Ref__Boolean_value $t@417 $r) (invOf@425 $r)))))
(assert (forall (($r $Ref)) (!
  (implies
    (and
      (ite
        (and (<= 0 (invOf@430 $r)) (< (invOf@430 $r) $t@414))
        (< $Perm.No $k@429)
        false)
      ($Set.in $r ($FVF.domain_Ref__Boolean_value fvf@459)))
    (=
      ($FVF.lookup_Ref__Boolean_value fvf@459 $r)
      ($FVF.lookup_Ref__Boolean_value $t@407 $r)))
  :pattern (($FVF.lookup_Ref__Boolean_value fvf@459 $r) (invOf@430 $r))
  :pattern (($FVF.lookup_Ref__Boolean_value $t@407 $r) (invOf@430 $r)))))
(pop) ; 7
(assert (forall ((k@458 Int)) (!
  (iff
    ($Set.in ($Seq.index $t@420 k@458) ($FVF.domain_Ref__Boolean_value fvf@459))
    (and (and (>= k@458 $t@414) (< k@458 (+ j@400 1))) (not (<= $t@116 $t@123))))
  :pattern (($Set.in
    ($Seq.index $t@420 k@458)
    ($FVF.domain_Ref__Boolean_value fvf@459))))))
(assert (forall (($r $Ref)) (!
  (implies
    (and
      (= $r ($Seq.index $t@420 j@400))
      ($Set.in $r ($FVF.domain_Ref__Boolean_value fvf@459)))
    (=
      ($FVF.lookup_Ref__Boolean_value fvf@459 $r)
      ($FVF.lookup_Ref__Boolean_value fvf@434 $r)))
  :pattern (($FVF.lookup_Ref__Boolean_value fvf@459 $r))
  :pattern (($FVF.lookup_Ref__Boolean_value fvf@434 $r)))))
(assert (forall (($r $Ref)) (!
  (implies
    (and
      (<
        $Perm.No
        (-
          (ite
            (and (<= 0 (invOf@425 $r)) (< (invOf@425 $r) $t@421))
            $Perm.Write
            $Perm.No)
          ($permsTaken35 $r)))
      ($Set.in $r ($FVF.domain_Ref__Boolean_value fvf@459)))
    (=
      ($FVF.lookup_Ref__Boolean_value fvf@459 $r)
      ($FVF.lookup_Ref__Boolean_value $t@417 $r)))
  :pattern (($FVF.lookup_Ref__Boolean_value fvf@459 $r) (invOf@425 $r))
  :pattern (($FVF.lookup_Ref__Boolean_value $t@417 $r) (invOf@425 $r)))))
(assert (forall (($r $Ref)) (!
  (implies
    (and
      (ite
        (and (<= 0 (invOf@430 $r)) (< (invOf@430 $r) $t@414))
        (< $Perm.No $k@429)
        false)
      ($Set.in $r ($FVF.domain_Ref__Boolean_value fvf@459)))
    (=
      ($FVF.lookup_Ref__Boolean_value fvf@459 $r)
      ($FVF.lookup_Ref__Boolean_value $t@407 $r)))
  :pattern (($FVF.lookup_Ref__Boolean_value fvf@459 $r) (invOf@430 $r))
  :pattern (($FVF.lookup_Ref__Boolean_value $t@407 $r) (invOf@430 $r)))))
(set-option :timeout 0)
(push) ; 7
(assert (not (forall ((k@458 Int)) (!
  (implies
    (and (>= k@458 $t@414) (< k@458 (+ j@400 1)))
    (not ($FVF.lookup_Ref__Boolean_value fvf@459 ($Seq.index $t@420 k@458))))
  :pattern (($Seq.index $t@420 k@458))))))
(check-sat)
; unsat
(pop) ; 7
; 0.02s
; (get-info :all-statistics)
(assert (forall ((k@458 Int)) (!
  (implies
    (and (>= k@458 $t@414) (< k@458 (+ j@400 1)))
    (not ($FVF.lookup_Ref__Boolean_value fvf@459 ($Seq.index $t@420 k@458))))
  :pattern (($Seq.index $t@420 k@458)))))
(pop) ; 6
(push) ; 6
; Establish loop invariant
(declare-const $k@460 $Perm)
(assert ($Perm.isValidVar $k@460))
(assert ($Perm.isReadVar $k@460 $Perm.Write))
(set-option :timeout 0)
(push) ; 7
(assert (not (or (= $k@460 $Perm.No) true)))
(check-sat)
; unsat
(pop) ; 7
; 0.00s
; (get-info :all-statistics)
(assert (< $k@460 (+ (- $k@115 $k@340) $k@383)))
; [eval] diz.Set__max > 0
(declare-const $k@461 $Perm)
(assert ($Perm.isValidVar $k@461))
(assert ($Perm.isReadVar $k@461 $Perm.Write))
(set-option :timeout 0)
(push) ; 7
(assert (not (or (= $k@461 $Perm.No) true)))
(check-sat)
; unsat
(pop) ; 7
; 0.00s
; (get-info :all-statistics)
(assert (< $k@461 (+ (- $k@117 $k@341) $k@384)))
; [eval] |diz.Set__contents| == diz.Set__max
; [eval] |diz.Set__contents|
(declare-const fvf@462 $FVF<Int>)
(declare-const fvf@463 $FVF<Int>)
(declare-const fvf@464 $FVF<$Seq<$Ref>>)
(declare-const fvf@465 $FVF<$Seq<$Ref>>)
(assert (= ($FVF.lookup_Set__max fvf@462 diz@101) $t@382))
(assert ($Set.equal ($FVF.domain_Set__max fvf@462) ($Set.singleton  diz@101)))
(assert (= ($FVF.lookup_Set__max fvf@463 x@102) $t@375))
(assert ($Set.equal ($FVF.domain_Set__max fvf@463) ($Set.singleton  x@102)))
(assert ($Seq.equal ($FVF.lookup_Set__contents fvf@464 diz@101) $t@381))
(assert ($Set.equal ($FVF.domain_Set__contents fvf@464) ($Set.singleton  diz@101)))
(assert ($Seq.equal ($FVF.lookup_Set__contents fvf@465 x@102) $t@372))
(assert ($Set.equal ($FVF.domain_Set__contents fvf@465) ($Set.singleton  x@102)))
(declare-const k@466 Int)
; [eval] (0 <= k) && (k < diz.Set__max)
; [eval] 0 <= k
(push) ; 7
(set-option :timeout 0)
(push) ; 8
(assert (not (not (<= 0 k@466))))
(check-sat)
; unknown
(pop) ; 8
; 0.00s
; (get-info :all-statistics)
(set-option :timeout 0)
(push) ; 8
(assert (not (<= 0 k@466)))
(check-sat)
; unknown
(pop) ; 8
; 0.00s
; (get-info :all-statistics)
(push) ; 8
; [then-branch 91] 0 <= k@466
(assert (<= 0 k@466))
; [eval] k < diz.Set__max
(set-option :timeout 0)
(push) ; 9
(assert (not (<
  $Perm.No
  (+
    (+ (- $k@115 $k@340) $k@383)
    (ite (= diz@101 x@102) (+ (- $k@122 $k@351) $k@387) $Perm.No)))))
(check-sat)
; unsat
(pop) ; 9
; 0.00s
; (get-info :all-statistics)
(declare-const fvf@467 $FVF<Int>)
(assert (implies
  (< $Perm.No (+ (- $k@115 $k@340) $k@383))
  (=
    ($FVF.lookup_Set__max fvf@467 diz@101)
    ($FVF.lookup_Set__max fvf@462 diz@101))))
(assert (implies
  (ite (= diz@101 x@102) (< $Perm.No (+ (- $k@122 $k@351) $k@387)) false)
  (=
    ($FVF.lookup_Set__max fvf@467 diz@101)
    ($FVF.lookup_Set__max fvf@463 diz@101))))
(assert ($Set.equal ($FVF.domain_Set__max fvf@467) ($Set.singleton  diz@101)))
(pop) ; 8
(push) ; 8
; [else-branch 91] !0 <= k@466
(assert (not (<= 0 k@466)))
(pop) ; 8
(pop) ; 7
(assert ($Set.equal ($FVF.domain_Set__max fvf@467) ($Set.singleton  diz@101)))
(assert (implies
  (ite (= diz@101 x@102) (< $Perm.No (+ (- $k@122 $k@351) $k@387)) false)
  (=
    ($FVF.lookup_Set__max fvf@467 diz@101)
    ($FVF.lookup_Set__max fvf@463 diz@101))))
(assert (implies
  (< $Perm.No (+ (- $k@115 $k@340) $k@383))
  (=
    ($FVF.lookup_Set__max fvf@467 diz@101)
    ($FVF.lookup_Set__max fvf@462 diz@101))))
(set-option :timeout 0)
(push) ; 7
(assert (not (not (and (<= 0 k@466) (< k@466 ($FVF.lookup_Set__max fvf@467 diz@101))))))
(check-sat)
; unknown
(pop) ; 7
; 0.00s
; (get-info :all-statistics)
(assert (and (<= 0 k@466) (< k@466 ($FVF.lookup_Set__max fvf@467 diz@101))))
; [eval] diz.Set__contents[k]
(set-option :timeout 0)
(push) ; 7
(assert (not (<
  $Perm.No
  (+
    (+ (- $k@117 $k@341) $k@384)
    (ite (= diz@101 x@102) (+ (- $k@124 $k@352) $k@388) $Perm.No)))))
(check-sat)
; unsat
(pop) ; 7
; 0.00s
; (get-info :all-statistics)
(declare-const fvf@468 $FVF<$Seq<$Ref>>)
(assert (implies
  (< $Perm.No (+ (- $k@117 $k@341) $k@384))
  ($Seq.equal
    ($FVF.lookup_Set__contents fvf@468 diz@101)
    ($FVF.lookup_Set__contents fvf@464 diz@101))))
(assert (implies
  (ite (= diz@101 x@102) (< $Perm.No (+ (- $k@124 $k@352) $k@388)) false)
  ($Seq.equal
    ($FVF.lookup_Set__contents fvf@468 diz@101)
    ($FVF.lookup_Set__contents fvf@465 diz@101))))
(assert ($Set.equal ($FVF.domain_Set__contents fvf@468) ($Set.singleton  diz@101)))
(set-option :timeout 0)
(push) ; 7
(assert (not (forall (($x Int) ($y Int)) (!
  (implies
    (and
      (and (<= 0 $x) (< $x ($FVF.lookup_Set__max fvf@467 diz@101)))
      (and (<= 0 $y) (< $y ($FVF.lookup_Set__max fvf@467 diz@101)))
      (=
        ($Seq.index ($FVF.lookup_Set__contents fvf@468 diz@101) $x)
        ($Seq.index ($FVF.lookup_Set__contents fvf@468 diz@101) $y)))
    (= $x $y))
  :pattern (($Seq.index ($FVF.lookup_Set__contents fvf@468 diz@101) $x) ($Seq.index
    ($FVF.lookup_Set__contents fvf@468 diz@101)
    $y))))))
(check-sat)
; unsat
(pop) ; 7
; 0.00s
; (get-info :all-statistics)
(declare-fun invOf@469 ($Ref) Int)
(assert (forall (($r $Ref)) (!
  (implies
    (and
      (<= 0 (invOf@469 $r))
      (< (invOf@469 $r) ($FVF.lookup_Set__max fvf@467 diz@101)))
    (=
      ($Seq.index ($FVF.lookup_Set__contents fvf@468 diz@101) (invOf@469 $r))
      $r))
  :pattern ((invOf@469 $r)))))
(assert (forall ((k@466 Int)) (!
  (implies
    (and (<= 0 k@466) (< k@466 ($FVF.lookup_Set__max fvf@467 diz@101)))
    (=
      (invOf@469 ($Seq.index ($FVF.lookup_Set__contents fvf@468 diz@101) k@466))
      k@466))
  :pattern (($Seq.index ($FVF.lookup_Set__contents fvf@468 diz@101) k@466)))))
(declare-const fvf@470 $FVF<Bool>)
; Precomputing split data for Lookup(Set__contents,fvf@468,diz@101)[k@466].Ref__Boolean_value # W
(define-fun $permsTaken43 (($r $Ref)) $Perm
  ($Perm.min
    (ite
      (and
        (<= 0 (invOf@469 $r))
        (< (invOf@469 $r) ($FVF.lookup_Set__max fvf@467 diz@101)))
      $Perm.Write
      $Perm.No)
    (ite
      (= $r ($Seq.index ($FVF.lookup_Set__contents fvf@468 diz@101) k@466))
      (ite (and (<= 0 (invOf@391 $r)) (< (invOf@391 $r) $t@375)) $k@390 $Perm.No)
      $Perm.No)))
(define-fun $permsTaken44 (($r $Ref)) $Perm
  ($Perm.min
    (-
      (ite
        (and
          (<= 0 (invOf@469 $r))
          (< (invOf@469 $r) ($FVF.lookup_Set__max fvf@467 diz@101)))
        $Perm.Write
        $Perm.No)
      ($permsTaken43 $r))
    (ite
      (= $r ($Seq.index ($FVF.lookup_Set__contents fvf@468 diz@101) k@466))
      (ite
        (and (<= 0 (invOf@386 $r)) (< (invOf@386 $r) $t@382))
        $Perm.Write
        $Perm.No)
      $Perm.No)))
(define-fun $permsTaken45 (($r $Ref)) $Perm
  ($Perm.min
    (-
      (-
        (ite
          (and
            (<= 0 (invOf@469 $r))
            (< (invOf@469 $r) ($FVF.lookup_Set__max fvf@467 diz@101)))
          $Perm.Write
          $Perm.No)
        ($permsTaken43 $r))
      ($permsTaken44 $r))
    (ite
      (= $r ($Seq.index ($FVF.lookup_Set__contents fvf@468 diz@101) k@466))
      (-
        (-
          (ite
            (and (<= 0 (invOf@129 $r)) (< (invOf@129 $r) $t@123))
            $k@127
            $Perm.No)
          ($permsTaken31 $r))
        ($permsTaken33 $r))
      $Perm.No)))
(define-fun $permsTaken46 (($r $Ref)) $Perm
  ($Perm.min
    (-
      (-
        (-
          (ite
            (and
              (<= 0 (invOf@469 $r))
              (< (invOf@469 $r) ($FVF.lookup_Set__max fvf@467 diz@101)))
            $Perm.Write
            $Perm.No)
          ($permsTaken43 $r))
        ($permsTaken44 $r))
      ($permsTaken45 $r))
    (ite
      (= $r ($Seq.index ($FVF.lookup_Set__contents fvf@468 diz@101) k@466))
      (-
        (-
          (ite
            (and (<= 0 (invOf@121 $r)) (< (invOf@121 $r) $t@116))
            $Perm.Write
            $Perm.No)
          ($permsTaken32 $r))
        ($permsTaken34 $r))
      $Perm.No)))
; Done precomputing, updating quantified heap chunks
; Chunk depleted?
(set-option :timeout 500)
(push) ; 7
(assert (not (forall (($r $Ref)) (!
  (=
    (-
      (ite (and (<= 0 (invOf@391 $r)) (< (invOf@391 $r) $t@375)) $k@390 $Perm.No)
      ($permsTaken43 $r))
    $Perm.No)
  ))))
(check-sat)
; unknown
(pop) ; 7
; 0.50s
; (get-info :all-statistics)
; Enough permissions taken?
(set-option :timeout 500)
(push) ; 7
(assert (not (=
  (-
    (ite
      (and
        (<=
          0
          (invOf@469 ($Seq.index
            ($FVF.lookup_Set__contents fvf@468 diz@101)
            k@466)))
        (<
          (invOf@469 ($Seq.index
            ($FVF.lookup_Set__contents fvf@468 diz@101)
            k@466))
          ($FVF.lookup_Set__max fvf@467 diz@101)))
      $Perm.Write
      $Perm.No)
    ($permsTaken43 ($Seq.index ($FVF.lookup_Set__contents fvf@468 diz@101) k@466)))
  $Perm.No)))
(check-sat)
; unknown
(pop) ; 7
; 0.09s
; (get-info :all-statistics)
; Chunk depleted?
(set-option :timeout 500)
(push) ; 7
(assert (not (forall (($r $Ref)) (!
  (=
    (-
      (ite
        (and (<= 0 (invOf@386 $r)) (< (invOf@386 $r) $t@382))
        $Perm.Write
        $Perm.No)
      ($permsTaken44 $r))
    $Perm.No)
  ))))
(check-sat)
; unknown
(pop) ; 7
; 0.50s
; (get-info :all-statistics)
; Enough permissions taken?
(set-option :timeout 500)
(push) ; 7
(assert (not (=
  (-
    (-
      (ite
        (and
          (<=
            0
            (invOf@469 ($Seq.index
              ($FVF.lookup_Set__contents fvf@468 diz@101)
              k@466)))
          (<
            (invOf@469 ($Seq.index
              ($FVF.lookup_Set__contents fvf@468 diz@101)
              k@466))
            ($FVF.lookup_Set__max fvf@467 diz@101)))
        $Perm.Write
        $Perm.No)
      ($permsTaken43 ($Seq.index
        ($FVF.lookup_Set__contents fvf@468 diz@101)
        k@466)))
    ($permsTaken44 ($Seq.index ($FVF.lookup_Set__contents fvf@468 diz@101) k@466)))
  $Perm.No)))
(check-sat)
; unsat
(pop) ; 7
; 0.01s
; (get-info :all-statistics)
; Final check that enough permissions have been taken
; Done splitting
(assert (forall (($r $Ref)) (!
  (implies
    (and
      (<
        $Perm.No
        (-
          (-
            (ite
              (and (<= 0 (invOf@121 $r)) (< (invOf@121 $r) $t@116))
              $Perm.Write
              $Perm.No)
            ($permsTaken32 $r))
          ($permsTaken34 $r)))
      ($Set.in $r ($FVF.domain_Ref__Boolean_value fvf@470)))
    (=
      ($FVF.lookup_Ref__Boolean_value fvf@470 $r)
      ($FVF.lookup_Ref__Boolean_value $t@120 $r)))
  :pattern (($FVF.lookup_Ref__Boolean_value fvf@470 $r) (invOf@121 $r))
  :pattern (($FVF.lookup_Ref__Boolean_value $t@120 $r) (invOf@121 $r)))))
(assert (forall (($r $Ref)) (!
  (implies
    (and
      (<
        $Perm.No
        (-
          (-
            (ite
              (and (<= 0 (invOf@129 $r)) (< (invOf@129 $r) $t@123))
              $k@127
              $Perm.No)
            ($permsTaken31 $r))
          ($permsTaken33 $r)))
      ($Set.in $r ($FVF.domain_Ref__Boolean_value fvf@470)))
    (=
      ($FVF.lookup_Ref__Boolean_value fvf@470 $r)
      ($FVF.lookup_Ref__Boolean_value $t@128 $r)))
  :pattern (($FVF.lookup_Ref__Boolean_value fvf@470 $r) (invOf@129 $r))
  :pattern (($FVF.lookup_Ref__Boolean_value $t@128 $r) (invOf@129 $r)))))
(assert (forall (($r $Ref)) (!
  (implies
    (and
      (and (<= 0 (invOf@386 $r)) (< (invOf@386 $r) $t@382))
      ($Set.in $r ($FVF.domain_Ref__Boolean_value fvf@470)))
    (=
      ($FVF.lookup_Ref__Boolean_value fvf@470 $r)
      ($FVF.lookup_Ref__Boolean_value $t@378 $r)))
  :pattern (($FVF.lookup_Ref__Boolean_value fvf@470 $r) (invOf@386 $r))
  :pattern (($FVF.lookup_Ref__Boolean_value $t@378 $r) (invOf@386 $r)))))
(assert (forall (($r $Ref)) (!
  (implies
    (and
      (ite
        (and (<= 0 (invOf@391 $r)) (< (invOf@391 $r) $t@375))
        (< $Perm.No $k@390)
        false)
      ($Set.in $r ($FVF.domain_Ref__Boolean_value fvf@470)))
    (=
      ($FVF.lookup_Ref__Boolean_value fvf@470 $r)
      ($FVF.lookup_Ref__Boolean_value $t@368 $r)))
  :pattern (($FVF.lookup_Ref__Boolean_value fvf@470 $r) (invOf@391 $r))
  :pattern (($FVF.lookup_Ref__Boolean_value $t@368 $r) (invOf@391 $r)))))
(assert (forall (($r $Ref)) (!
  (iff
    ($Set.in $r ($FVF.domain_Ref__Boolean_value fvf@470))
    (and
      (<= 0 (invOf@469 $r))
      (< (invOf@469 $r) ($FVF.lookup_Set__max fvf@467 diz@101))))
  :pattern (($Set.in $r ($FVF.domain_Ref__Boolean_value fvf@470))))))
; [eval] x != null
(declare-const $k@471 $Perm)
(assert ($Perm.isValidVar $k@471))
(assert ($Perm.isReadVar $k@471 $Perm.Write))
(set-option :timeout 0)
(push) ; 7
(assert (not (or (= $k@471 $Perm.No) true)))
(check-sat)
; unsat
(pop) ; 7
; 0.00s
; (get-info :all-statistics)
(assert (< $k@471 (+ (- $k@122 $k@351) $k@387)))
; [eval] x.Set__max > 0
(declare-const $k@472 $Perm)
(assert ($Perm.isValidVar $k@472))
(assert ($Perm.isReadVar $k@472 $Perm.Write))
(set-option :timeout 0)
(push) ; 7
(assert (not (or (= $k@472 $Perm.No) true)))
(check-sat)
; unsat
(pop) ; 7
; 0.00s
; (get-info :all-statistics)
(assert (< $k@472 (+ (- $k@124 $k@352) $k@388)))
; [eval] diz.Set__max > x.Set__max
; [eval] (j >= x.Set__max) && (j <= diz.Set__max)
; [eval] j >= x.Set__max
(push) ; 7
(set-option :timeout 0)
(push) ; 8
(assert (not (not (>= j@272 $t@375))))
(check-sat)
; unknown
(pop) ; 8
; 0.00s
; (get-info :all-statistics)
(set-option :timeout 0)
(push) ; 8
(assert (not (>= j@272 $t@375)))
(check-sat)
; unsat
(pop) ; 8
; 0.00s
; (get-info :all-statistics)
(push) ; 8
; [then-branch 92] j@272 >= $t@375
(assert (>= j@272 $t@375))
; [eval] j <= diz.Set__max
(pop) ; 8
; [dead else-branch 92] !j@272 >= $t@375
(pop) ; 7
(set-option :timeout 0)
(push) ; 7
(assert (not (and (>= j@272 $t@375) (<= j@272 $t@382))))
(check-sat)
; unsat
(pop) ; 7
; 0.00s
; (get-info :all-statistics)
(assert (and (>= j@272 $t@375) (<= j@272 $t@382)))
(declare-const fvf@473 $FVF<Int>)
(declare-const fvf@474 $FVF<Int>)
(declare-const fvf@475 $FVF<$Seq<$Ref>>)
(declare-const fvf@476 $FVF<$Seq<$Ref>>)
(assert (= ($FVF.lookup_Set__max fvf@473 diz@101) $t@382))
(assert ($Set.equal ($FVF.domain_Set__max fvf@473) ($Set.singleton  diz@101)))
(assert (= ($FVF.lookup_Set__max fvf@474 x@102) $t@375))
(assert ($Set.equal ($FVF.domain_Set__max fvf@474) ($Set.singleton  x@102)))
(assert ($Seq.equal ($FVF.lookup_Set__contents fvf@475 diz@101) $t@381))
(assert ($Set.equal ($FVF.domain_Set__contents fvf@475) ($Set.singleton  diz@101)))
(assert ($Seq.equal ($FVF.lookup_Set__contents fvf@476 x@102) $t@372))
(assert ($Set.equal ($FVF.domain_Set__contents fvf@476) ($Set.singleton  x@102)))
(declare-const k@477 Int)
; [eval] (0 <= k) && (k < x.Set__max)
; [eval] 0 <= k
(push) ; 7
(set-option :timeout 0)
(push) ; 8
(assert (not (not (<= 0 k@477))))
(check-sat)
; unknown
(pop) ; 8
; 0.00s
; (get-info :all-statistics)
(set-option :timeout 0)
(push) ; 8
(assert (not (<= 0 k@477)))
(check-sat)
; unknown
(pop) ; 8
; 0.00s
; (get-info :all-statistics)
(push) ; 8
; [then-branch 93] 0 <= k@477
(assert (<= 0 k@477))
; [eval] k < x.Set__max
(set-option :timeout 0)
(push) ; 9
(assert (not (<
  $Perm.No
  (+
    (ite (= x@102 diz@101) (+ (- $k@115 $k@340) $k@383) $Perm.No)
    (+ (- $k@122 $k@351) $k@387)))))
(check-sat)
; unsat
(pop) ; 9
; 0.00s
; (get-info :all-statistics)
(declare-const fvf@478 $FVF<Int>)
(assert (implies
  (ite (= x@102 diz@101) (< $Perm.No (+ (- $k@115 $k@340) $k@383)) false)
  (= ($FVF.lookup_Set__max fvf@478 x@102) ($FVF.lookup_Set__max fvf@473 x@102))))
(assert (implies
  (< $Perm.No (+ (- $k@122 $k@351) $k@387))
  (= ($FVF.lookup_Set__max fvf@478 x@102) ($FVF.lookup_Set__max fvf@474 x@102))))
(assert ($Set.equal ($FVF.domain_Set__max fvf@478) ($Set.singleton  x@102)))
(pop) ; 8
(push) ; 8
; [else-branch 93] !0 <= k@477
(assert (not (<= 0 k@477)))
(pop) ; 8
(pop) ; 7
(assert ($Set.equal ($FVF.domain_Set__max fvf@478) ($Set.singleton  x@102)))
(assert (implies
  (< $Perm.No (+ (- $k@122 $k@351) $k@387))
  (= ($FVF.lookup_Set__max fvf@478 x@102) ($FVF.lookup_Set__max fvf@474 x@102))))
(assert (implies
  (ite (= x@102 diz@101) (< $Perm.No (+ (- $k@115 $k@340) $k@383)) false)
  (= ($FVF.lookup_Set__max fvf@478 x@102) ($FVF.lookup_Set__max fvf@473 x@102))))
(set-option :timeout 0)
(push) ; 7
(assert (not (not (and (<= 0 k@477) (< k@477 ($FVF.lookup_Set__max fvf@478 x@102))))))
(check-sat)
; unknown
(pop) ; 7
; 0.00s
; (get-info :all-statistics)
(assert (and (<= 0 k@477) (< k@477 ($FVF.lookup_Set__max fvf@478 x@102))))
(declare-const $k@479 $Perm)
(assert ($Perm.isValidVar $k@479))
(assert ($Perm.isReadVar $k@479 $Perm.Write))
(set-option :timeout 0)
(push) ; 7
(assert (not (or (= $k@479 $Perm.No) true)))
(check-sat)
; unsat
(pop) ; 7
; 0.00s
; (get-info :all-statistics)
; [eval] x.Set__contents[k]
(set-option :timeout 0)
(push) ; 7
(assert (not (<
  $Perm.No
  (+
    (ite (= x@102 diz@101) (+ (- $k@117 $k@341) $k@384) $Perm.No)
    (+ (- $k@124 $k@352) $k@388)))))
(check-sat)
; unsat
(pop) ; 7
; 0.00s
; (get-info :all-statistics)
(declare-const fvf@480 $FVF<$Seq<$Ref>>)
(assert (implies
  (ite (= x@102 diz@101) (< $Perm.No (+ (- $k@117 $k@341) $k@384)) false)
  ($Seq.equal
    ($FVF.lookup_Set__contents fvf@480 x@102)
    ($FVF.lookup_Set__contents fvf@475 x@102))))
(assert (implies
  (< $Perm.No (+ (- $k@124 $k@352) $k@388))
  ($Seq.equal
    ($FVF.lookup_Set__contents fvf@480 x@102)
    ($FVF.lookup_Set__contents fvf@476 x@102))))
(assert ($Set.equal ($FVF.domain_Set__contents fvf@480) ($Set.singleton  x@102)))
(set-option :timeout 0)
(push) ; 7
(assert (not (forall (($x Int) ($y Int)) (!
  (implies
    (and
      (and (<= 0 $x) (< $x ($FVF.lookup_Set__max fvf@478 x@102)))
      (and (<= 0 $y) (< $y ($FVF.lookup_Set__max fvf@478 x@102)))
      (=
        ($Seq.index ($FVF.lookup_Set__contents fvf@480 x@102) $x)
        ($Seq.index ($FVF.lookup_Set__contents fvf@480 x@102) $y)))
    (= $x $y))
  :pattern (($Seq.index ($FVF.lookup_Set__contents fvf@480 x@102) $x) ($Seq.index
    ($FVF.lookup_Set__contents fvf@480 x@102)
    $y))))))
(check-sat)
; unsat
(pop) ; 7
; 0.00s
; (get-info :all-statistics)
(declare-fun invOf@481 ($Ref) Int)
(assert (forall (($r $Ref)) (!
  (implies
    (and
      (<= 0 (invOf@481 $r))
      (< (invOf@481 $r) ($FVF.lookup_Set__max fvf@478 x@102)))
    (= ($Seq.index ($FVF.lookup_Set__contents fvf@480 x@102) (invOf@481 $r)) $r))
  :pattern ((invOf@481 $r)))))
(assert (forall ((k@477 Int)) (!
  (implies
    (and (<= 0 k@477) (< k@477 ($FVF.lookup_Set__max fvf@478 x@102)))
    (=
      (invOf@481 ($Seq.index ($FVF.lookup_Set__contents fvf@480 x@102) k@477))
      k@477))
  :pattern (($Seq.index ($FVF.lookup_Set__contents fvf@480 x@102) k@477)))))
(declare-const fvf@482 $FVF<Bool>)
; Precomputing split data for Lookup(Set__contents,fvf@480,x@102)[k@477].Ref__Boolean_value # $k@479
(define-fun $permsTaken47 (($r $Ref)) $Perm
  ($Perm.min
    (ite
      (and
        (<= 0 (invOf@481 $r))
        (< (invOf@481 $r) ($FVF.lookup_Set__max fvf@478 x@102)))
      $k@479
      $Perm.No)
    (ite
      (= $r ($Seq.index ($FVF.lookup_Set__contents fvf@480 x@102) k@477))
      (-
        (ite
          (and (<= 0 (invOf@391 $r)) (< (invOf@391 $r) $t@375))
          $k@390
          $Perm.No)
        ($permsTaken43 $r))
      $Perm.No)))
(define-fun $permsTaken48 (($r $Ref)) $Perm
  ($Perm.min
    (-
      (ite
        (and
          (<= 0 (invOf@481 $r))
          (< (invOf@481 $r) ($FVF.lookup_Set__max fvf@478 x@102)))
        $k@479
        $Perm.No)
      ($permsTaken47 $r))
    (ite
      (= $r ($Seq.index ($FVF.lookup_Set__contents fvf@480 x@102) k@477))
      (-
        (ite
          (and (<= 0 (invOf@386 $r)) (< (invOf@386 $r) $t@382))
          $Perm.Write
          $Perm.No)
        ($permsTaken44 $r))
      $Perm.No)))
(define-fun $permsTaken49 (($r $Ref)) $Perm
  ($Perm.min
    (-
      (-
        (ite
          (and
            (<= 0 (invOf@481 $r))
            (< (invOf@481 $r) ($FVF.lookup_Set__max fvf@478 x@102)))
          $k@479
          $Perm.No)
        ($permsTaken47 $r))
      ($permsTaken48 $r))
    (ite
      (= $r ($Seq.index ($FVF.lookup_Set__contents fvf@480 x@102) k@477))
      (-
        (-
          (ite
            (and (<= 0 (invOf@129 $r)) (< (invOf@129 $r) $t@123))
            $k@127
            $Perm.No)
          ($permsTaken31 $r))
        ($permsTaken33 $r))
      $Perm.No)))
(define-fun $permsTaken50 (($r $Ref)) $Perm
  ($Perm.min
    (-
      (-
        (-
          (ite
            (and
              (<= 0 (invOf@481 $r))
              (< (invOf@481 $r) ($FVF.lookup_Set__max fvf@478 x@102)))
            $k@479
            $Perm.No)
          ($permsTaken47 $r))
        ($permsTaken48 $r))
      ($permsTaken49 $r))
    (ite
      (= $r ($Seq.index ($FVF.lookup_Set__contents fvf@480 x@102) k@477))
      (-
        (-
          (ite
            (and (<= 0 (invOf@121 $r)) (< (invOf@121 $r) $t@116))
            $Perm.Write
            $Perm.No)
          ($permsTaken32 $r))
        ($permsTaken34 $r))
      $Perm.No)))
; Done precomputing, updating quantified heap chunks
; Constrain original permissions $k@479
(assert (forall (($r $Ref)) (!
  (implies
    (not
      (=
        (-
          (ite
            (and (<= 0 (invOf@391 $r)) (< (invOf@391 $r) $t@375))
            $k@390
            $Perm.No)
          ($permsTaken43 $r))
        $Perm.No))
    (<
      (ite
        (and
          (<= 0 (invOf@481 $r))
          (< (invOf@481 $r) ($FVF.lookup_Set__max fvf@478 x@102)))
        $k@479
        $Perm.No)
      (-
        (ite
          (and (<= 0 (invOf@391 $r)) (< (invOf@391 $r) $t@375))
          $k@390
          $Perm.No)
        ($permsTaken43 $r))))
  :pattern ((invOf@391 $r))
  :pattern ((invOf@391 $r))
  :pattern ((invOf@481 $r))
  :pattern ((invOf@481 $r))
  :pattern ((invOf@391 $r))
  :pattern ((invOf@391 $r)))))
; Enough permissions taken?
(set-option :timeout 500)
(push) ; 7
(assert (not (=
  (-
    (ite
      (and
        (<=
          0
          (invOf@481 ($Seq.index ($FVF.lookup_Set__contents fvf@480 x@102) k@477)))
        (<
          (invOf@481 ($Seq.index ($FVF.lookup_Set__contents fvf@480 x@102) k@477))
          ($FVF.lookup_Set__max fvf@478 x@102)))
      $k@479
      $Perm.No)
    ($permsTaken47 ($Seq.index ($FVF.lookup_Set__contents fvf@480 x@102) k@477)))
  $Perm.No)))
(check-sat)
; unknown
(pop) ; 7
; 0.50s
; (get-info :all-statistics)
; Constrain original permissions $k@479
(assert (forall (($r $Ref)) (!
  (implies
    (not
      (=
        (-
          (ite
            (and (<= 0 (invOf@386 $r)) (< (invOf@386 $r) $t@382))
            $Perm.Write
            $Perm.No)
          ($permsTaken44 $r))
        $Perm.No))
    (<
      (ite
        (and
          (<= 0 (invOf@481 $r))
          (< (invOf@481 $r) ($FVF.lookup_Set__max fvf@478 x@102)))
        $k@479
        $Perm.No)
      (-
        (ite
          (and (<= 0 (invOf@386 $r)) (< (invOf@386 $r) $t@382))
          $Perm.Write
          $Perm.No)
        ($permsTaken44 $r))))
  :pattern ((invOf@386 $r))
  :pattern ((invOf@386 $r))
  :pattern ((invOf@481 $r))
  :pattern ((invOf@481 $r))
  :pattern ((invOf@386 $r))
  :pattern ((invOf@386 $r)))))
; Enough permissions taken?
(set-option :timeout 500)
(push) ; 7
(assert (not (=
  (-
    (-
      (ite
        (and
          (<=
            0
            (invOf@481 ($Seq.index
              ($FVF.lookup_Set__contents fvf@480 x@102)
              k@477)))
          (<
            (invOf@481 ($Seq.index
              ($FVF.lookup_Set__contents fvf@480 x@102)
              k@477))
            ($FVF.lookup_Set__max fvf@478 x@102)))
        $k@479
        $Perm.No)
      ($permsTaken47 ($Seq.index ($FVF.lookup_Set__contents fvf@480 x@102) k@477)))
    ($permsTaken48 ($Seq.index ($FVF.lookup_Set__contents fvf@480 x@102) k@477)))
  $Perm.No)))
(check-sat)
; unsat
(pop) ; 7
; 0.02s
; (get-info :all-statistics)
; Final check that enough permissions have been taken
; Done splitting
(assert (forall (($r $Ref)) (!
  (implies
    (and
      (<
        $Perm.No
        (-
          (-
            (ite
              (and (<= 0 (invOf@121 $r)) (< (invOf@121 $r) $t@116))
              $Perm.Write
              $Perm.No)
            ($permsTaken32 $r))
          ($permsTaken34 $r)))
      ($Set.in $r ($FVF.domain_Ref__Boolean_value fvf@482)))
    (=
      ($FVF.lookup_Ref__Boolean_value fvf@482 $r)
      ($FVF.lookup_Ref__Boolean_value $t@120 $r)))
  :pattern (($FVF.lookup_Ref__Boolean_value fvf@482 $r) (invOf@121 $r))
  :pattern (($FVF.lookup_Ref__Boolean_value $t@120 $r) (invOf@121 $r)))))
(assert (forall (($r $Ref)) (!
  (implies
    (and
      (<
        $Perm.No
        (-
          (-
            (ite
              (and (<= 0 (invOf@129 $r)) (< (invOf@129 $r) $t@123))
              $k@127
              $Perm.No)
            ($permsTaken31 $r))
          ($permsTaken33 $r)))
      ($Set.in $r ($FVF.domain_Ref__Boolean_value fvf@482)))
    (=
      ($FVF.lookup_Ref__Boolean_value fvf@482 $r)
      ($FVF.lookup_Ref__Boolean_value $t@128 $r)))
  :pattern (($FVF.lookup_Ref__Boolean_value fvf@482 $r) (invOf@129 $r))
  :pattern (($FVF.lookup_Ref__Boolean_value $t@128 $r) (invOf@129 $r)))))
(assert (forall (($r $Ref)) (!
  (implies
    (and
      (<
        $Perm.No
        (-
          (ite
            (and (<= 0 (invOf@386 $r)) (< (invOf@386 $r) $t@382))
            $Perm.Write
            $Perm.No)
          ($permsTaken44 $r)))
      ($Set.in $r ($FVF.domain_Ref__Boolean_value fvf@482)))
    (=
      ($FVF.lookup_Ref__Boolean_value fvf@482 $r)
      ($FVF.lookup_Ref__Boolean_value $t@378 $r)))
  :pattern (($FVF.lookup_Ref__Boolean_value fvf@482 $r) (invOf@386 $r))
  :pattern (($FVF.lookup_Ref__Boolean_value $t@378 $r) (invOf@386 $r)))))
(assert (forall (($r $Ref)) (!
  (implies
    (and
      (<
        $Perm.No
        (-
          (ite
            (and (<= 0 (invOf@391 $r)) (< (invOf@391 $r) $t@375))
            $k@390
            $Perm.No)
          ($permsTaken43 $r)))
      ($Set.in $r ($FVF.domain_Ref__Boolean_value fvf@482)))
    (=
      ($FVF.lookup_Ref__Boolean_value fvf@482 $r)
      ($FVF.lookup_Ref__Boolean_value $t@368 $r)))
  :pattern (($FVF.lookup_Ref__Boolean_value fvf@482 $r) (invOf@391 $r))
  :pattern (($FVF.lookup_Ref__Boolean_value $t@368 $r) (invOf@391 $r)))))
(assert (forall (($r $Ref)) (!
  (iff
    ($Set.in $r ($FVF.domain_Ref__Boolean_value fvf@482))
    (and
      (<= 0 (invOf@481 $r))
      (< (invOf@481 $r) ($FVF.lookup_Set__max fvf@478 x@102))))
  :pattern (($Set.in $r ($FVF.domain_Ref__Boolean_value fvf@482))))))
; [eval] (forall k: Int :: (k >= x.Set__max) && (k < j) ==> !diz.Set__contents[k].Ref__Boolean_value)
(declare-const k@483 Int)
(push) ; 7
; [eval] (k >= x.Set__max) && (k < j) ==> !diz.Set__contents[k].Ref__Boolean_value
; [eval] (k >= x.Set__max) && (k < j)
; [eval] k >= x.Set__max
(push) ; 8
(set-option :timeout 0)
(push) ; 9
(assert (not (not (>= k@483 $t@375))))
(check-sat)
; unknown
(pop) ; 9
; 0.00s
; (get-info :all-statistics)
(set-option :timeout 0)
(push) ; 9
(assert (not (>= k@483 $t@375)))
(check-sat)
; unknown
(pop) ; 9
; 0.00s
; (get-info :all-statistics)
(push) ; 9
; [then-branch 94] k@483 >= $t@375
(assert (>= k@483 $t@375))
; [eval] k < j
(pop) ; 9
(push) ; 9
; [else-branch 94] !k@483 >= $t@375
(assert (not (>= k@483 $t@375)))
(pop) ; 9
(pop) ; 8
(push) ; 8
(set-option :timeout 0)
(push) ; 9
(assert (not (not (and (>= k@483 $t@375) (< k@483 j@272)))))
(check-sat)
; unsat
(pop) ; 9
; 0.00s
; (get-info :all-statistics)
(set-option :timeout 0)
(push) ; 9
(assert (not (and (>= k@483 $t@375) (< k@483 j@272))))
(check-sat)
; unknown
(pop) ; 9
; 0.00s
; (get-info :all-statistics)
; [dead then-branch 95] k@483 >= $t@375 && k@483 < j@272
(push) ; 9
; [else-branch 95] !k@483 >= $t@375 && k@483 < j@272
(assert (not (and (>= k@483 $t@375) (< k@483 j@272))))
(pop) ; 9
(pop) ; 8
(pop) ; 7
(set-option :timeout 0)
(push) ; 7
(assert (not (forall ((k@483 Int)) (!
  true
  :pattern ()))))
(check-sat)
; unsat
(pop) ; 7
; 0.00s
; (get-info :all-statistics)
(assert (forall ((k@483 Int)) (!
  true
  :pattern ())))
; Continue after loop
(declare-const $t@484 $Snap)
(declare-const $t@485 $Snap)
(assert (= $t@484 ($Snap.combine $t@485 $Snap.unit)))
(declare-const $t@486 $Snap)
(assert (= $t@485 ($Snap.combine $t@486 $Snap.unit)))
(declare-const $t@487 $Snap)
(declare-const $t@488 $FVF<Bool>)
(assert (= $t@486 ($Snap.combine $t@487 ($SortWrappers.$FVF<Bool>To$Snap $t@488))))
(declare-const $t@489 $Snap)
(assert (= $t@487 ($Snap.combine $t@489 $Snap.unit)))
(declare-const $t@490 $Snap)
(assert (= $t@489 ($Snap.combine $t@490 $Snap.unit)))
(declare-const $t@491 $Snap)
(declare-const $t@492 $Seq<$Ref>)
(assert (= $t@490 ($Snap.combine $t@491 ($SortWrappers.$Seq<$Ref>To$Snap $t@492))))
(declare-const $t@493 $Snap)
(assert (= $t@491 ($Snap.combine $t@493 $Snap.unit)))
(declare-const $t@494 $Snap)
(declare-const $t@495 Int)
(assert (= $t@493 ($Snap.combine $t@494 ($SortWrappers.IntTo$Snap $t@495))))
(declare-const $t@496 $Snap)
(assert (= $t@494 ($Snap.combine $t@496 $Snap.unit)))
(declare-const $t@497 $Snap)
(declare-const $t@498 $FVF<Bool>)
(assert (= $t@496 ($Snap.combine $t@497 ($SortWrappers.$FVF<Bool>To$Snap $t@498))))
(declare-const $t@499 $Snap)
(assert (= $t@497 ($Snap.combine $t@499 $Snap.unit)))
(declare-const $t@500 Int)
(declare-const $t@501 $Seq<$Ref>)
(assert (=
  $t@499
  ($Snap.combine
    ($SortWrappers.IntTo$Snap $t@500)
    ($SortWrappers.$Seq<$Ref>To$Snap $t@501))))
(declare-const $t@502 Int)
(assert (=
  ($SortWrappers.IntTo$Snap $t@500)
  ($Snap.combine ($SortWrappers.IntTo$Snap $t@502) $Snap.unit)))
(declare-const $k@503 $Perm)
(assert ($Perm.isValidVar $k@503))
(assert ($Perm.isReadVar $k@503 $Perm.Write))
(assert (implies (< $Perm.No (- (+ (- $k@115 $k@340) $k@383) $k@460)) (= $t@502 $t@382)))
; [eval] diz.Set__max > 0
(set-option :timeout 0)
(push) ; 7
(assert (not (not (= (+ (- (+ (- $k@115 $k@340) $k@383) $k@460) $k@503) $Perm.No))))
(check-sat)
; unsat
(pop) ; 7
; 0.00s
; (get-info :all-statistics)
(assert (not (= (+ (- (+ (- $k@115 $k@340) $k@383) $k@460) $k@503) $Perm.No)))
(assert (> $t@502 0))
(declare-const $k@504 $Perm)
(assert ($Perm.isValidVar $k@504))
(assert ($Perm.isReadVar $k@504 $Perm.Write))
(assert (implies
  (< $Perm.No (- (+ (- $k@117 $k@341) $k@384) $k@461))
  ($Seq.equal $t@501 $t@381)))
; [eval] |diz.Set__contents| == diz.Set__max
; [eval] |diz.Set__contents|
(set-option :timeout 0)
(push) ; 7
(assert (not (not (= (+ (- (+ (- $k@117 $k@341) $k@384) $k@461) $k@504) $Perm.No))))
(check-sat)
; unsat
(pop) ; 7
; 0.00s
; (get-info :all-statistics)
(assert (not (= (+ (- (+ (- $k@117 $k@341) $k@384) $k@461) $k@504) $Perm.No)))
(assert (= ($Seq.length $t@501) $t@502))
(declare-const k@505 Int)
(push) ; 7
; [eval] (0 <= k) && (k < diz.Set__max)
; [eval] 0 <= k
(push) ; 8
(set-option :timeout 0)
(push) ; 9
(assert (not (not (<= 0 k@505))))
(check-sat)
; unknown
(pop) ; 9
; 0.01s
; (get-info :all-statistics)
(set-option :timeout 0)
(push) ; 9
(assert (not (<= 0 k@505)))
(check-sat)
; unknown
(pop) ; 9
; 0.01s
; (get-info :all-statistics)
(push) ; 9
; [then-branch 96] 0 <= k@505
(assert (<= 0 k@505))
; [eval] k < diz.Set__max
(pop) ; 9
(push) ; 9
; [else-branch 96] !0 <= k@505
(assert (not (<= 0 k@505)))
(pop) ; 9
(pop) ; 8
(assert (and (<= 0 k@505) (< k@505 $t@502)))
; [eval] diz.Set__contents[k]
(pop) ; 7
(declare-fun invOf@506 ($Ref) Int)
(assert (forall (($r $Ref)) (!
  (implies
    (and (<= 0 (invOf@506 $r)) (< (invOf@506 $r) $t@502))
    (= ($Seq.index $t@501 (invOf@506 $r)) $r))
  :pattern ((invOf@506 $r)))))
(assert (forall ((k@505 Int)) (!
  (implies
    (and (<= 0 k@505) (< k@505 $t@502))
    (= (invOf@506 ($Seq.index $t@501 k@505)) k@505))
  :pattern (($Seq.index $t@501 k@505)))))
(assert (forall ((k@505 Int)) (!
  (iff
    ($Set.in ($Seq.index $t@501 k@505) ($FVF.domain_Ref__Boolean_value $t@498))
    (and (<= 0 k@505) (< k@505 $t@502)))
  :pattern (($Set.in
    ($Seq.index $t@501 k@505)
    ($FVF.domain_Ref__Boolean_value $t@498))))))
(assert (forall ((k@505 Int)) (!
  (implies
    (and (<= 0 k@505) (< k@505 $t@502))
    (not (= ($Seq.index $t@501 k@505) $Ref.null)))
  :pattern (($Seq.index $t@501 k@505)))))
; [eval] x != null
(declare-const $k@507 $Perm)
(assert ($Perm.isValidVar $k@507))
(assert ($Perm.isReadVar $k@507 $Perm.Write))
(assert (implies (< $Perm.No (- (+ (- $k@122 $k@351) $k@387) $k@471)) (= $t@495 $t@375)))
; [eval] x.Set__max > 0
(set-option :timeout 0)
(push) ; 7
(assert (not (not (= (+ (- (+ (- $k@122 $k@351) $k@387) $k@471) $k@507) $Perm.No))))
(check-sat)
; unsat
(pop) ; 7
; 0.00s
; (get-info :all-statistics)
(assert (not (= (+ (- (+ (- $k@122 $k@351) $k@387) $k@471) $k@507) $Perm.No)))
(assert (> $t@495 0))
(declare-const $k@508 $Perm)
(assert ($Perm.isValidVar $k@508))
(assert ($Perm.isReadVar $k@508 $Perm.Write))
(assert (implies
  (< $Perm.No (- (+ (- $k@124 $k@352) $k@388) $k@472))
  ($Seq.equal $t@492 $t@372)))
; [eval] diz.Set__max > x.Set__max
(assert (> $t@502 $t@495))
; [eval] (j >= x.Set__max) && (j <= diz.Set__max)
; [eval] j >= x.Set__max
(push) ; 7
(set-option :timeout 0)
(push) ; 8
(assert (not (not (>= j@400 $t@495))))
(check-sat)
; unknown
(pop) ; 8
; 0.01s
; (get-info :all-statistics)
(set-option :timeout 0)
(push) ; 8
(assert (not (>= j@400 $t@495)))
(check-sat)
; unknown
(pop) ; 8
; 0.01s
; (get-info :all-statistics)
(push) ; 8
; [then-branch 97] j@400 >= $t@495
(assert (>= j@400 $t@495))
; [eval] j <= diz.Set__max
(pop) ; 8
(push) ; 8
; [else-branch 97] !j@400 >= $t@495
(assert (not (>= j@400 $t@495)))
(pop) ; 8
(pop) ; 7
(assert (and (>= j@400 $t@495) (<= j@400 $t@502)))
(declare-const k@509 Int)
(push) ; 7
; [eval] (0 <= k) && (k < x.Set__max)
; [eval] 0 <= k
(push) ; 8
(set-option :timeout 0)
(push) ; 9
(assert (not (not (<= 0 k@509))))
(check-sat)
; unknown
(pop) ; 9
; 0.01s
; (get-info :all-statistics)
(set-option :timeout 0)
(push) ; 9
(assert (not (<= 0 k@509)))
(check-sat)
; unknown
(pop) ; 9
; 0.01s
; (get-info :all-statistics)
(push) ; 9
; [then-branch 98] 0 <= k@509
(assert (<= 0 k@509))
; [eval] k < x.Set__max
(pop) ; 9
(push) ; 9
; [else-branch 98] !0 <= k@509
(assert (not (<= 0 k@509)))
(pop) ; 9
(pop) ; 8
(assert (and (<= 0 k@509) (< k@509 $t@495)))
; [eval] x.Set__contents[k]
(set-option :timeout 0)
(push) ; 8
(assert (not (not (= (+ (- (+ (- $k@124 $k@352) $k@388) $k@472) $k@508) $Perm.No))))
(check-sat)
; unsat
(pop) ; 8
; 0.00s
; (get-info :all-statistics)
(assert (not (= (+ (- (+ (- $k@124 $k@352) $k@388) $k@472) $k@508) $Perm.No)))
(declare-const $k@510 $Perm)
(assert ($Perm.isValidVar $k@510))
(assert ($Perm.isReadVar $k@510 $Perm.Write))
(pop) ; 7
(assert (not (= (+ (- (+ (- $k@124 $k@352) $k@388) $k@472) $k@508) $Perm.No)))
(assert ($Perm.isValidVar $k@510))
(assert ($Perm.isReadVar $k@510 $Perm.Write))
(declare-fun invOf@511 ($Ref) Int)
(assert (forall (($r $Ref)) (!
  (implies
    (and (<= 0 (invOf@511 $r)) (< (invOf@511 $r) $t@495))
    (= ($Seq.index $t@492 (invOf@511 $r)) $r))
  :pattern ((invOf@511 $r)))))
(assert (forall ((k@509 Int)) (!
  (implies
    (and (<= 0 k@509) (< k@509 $t@495))
    (= (invOf@511 ($Seq.index $t@492 k@509)) k@509))
  :pattern (($Seq.index $t@492 k@509)))))
(assert (forall ((k@509 Int)) (!
  (iff
    ($Set.in ($Seq.index $t@492 k@509) ($FVF.domain_Ref__Boolean_value $t@488))
    (and (<= 0 k@509) (< k@509 $t@495)))
  :pattern (($Set.in
    ($Seq.index $t@492 k@509)
    ($FVF.domain_Ref__Boolean_value $t@488))))))
(assert (forall ((k@509 Int)) (!
  (implies
    (and (and (<= 0 k@509) (< k@509 $t@495)) (< $Perm.No $k@510))
    (not (= ($Seq.index $t@492 k@509) $Ref.null)))
  :pattern (($Seq.index $t@492 k@509)))))
(assert (< $Perm.No $k@510))
; [eval] (forall k: Int :: (k >= x.Set__max) && (k < j) ==> !diz.Set__contents[k].Ref__Boolean_value)
(declare-const k@512 Int)
(push) ; 7
; [eval] (k >= x.Set__max) && (k < j) ==> !diz.Set__contents[k].Ref__Boolean_value
; [eval] (k >= x.Set__max) && (k < j)
; [eval] k >= x.Set__max
(push) ; 8
(set-option :timeout 0)
(push) ; 9
(assert (not (not (>= k@512 $t@495))))
(check-sat)
; unknown
(pop) ; 9
; 0.01s
; (get-info :all-statistics)
(set-option :timeout 0)
(push) ; 9
(assert (not (>= k@512 $t@495)))
(check-sat)
; unknown
(pop) ; 9
; 0.01s
; (get-info :all-statistics)
(push) ; 9
; [then-branch 99] k@512 >= $t@495
(assert (>= k@512 $t@495))
; [eval] k < j
(pop) ; 9
(push) ; 9
; [else-branch 99] !k@512 >= $t@495
(assert (not (>= k@512 $t@495)))
(pop) ; 9
(pop) ; 8
(push) ; 8
(set-option :timeout 0)
(push) ; 9
(assert (not (not (and (>= k@512 $t@495) (< k@512 j@400)))))
(check-sat)
; unknown
(pop) ; 9
; 0.00s
; (get-info :all-statistics)
(set-option :timeout 0)
(push) ; 9
(assert (not (and (>= k@512 $t@495) (< k@512 j@400))))
(check-sat)
; unknown
(pop) ; 9
; 0.01s
; (get-info :all-statistics)
(push) ; 9
; [then-branch 100] k@512 >= $t@495 && k@512 < j@400
(assert (and (>= k@512 $t@495) (< k@512 j@400)))
; [eval] !diz.Set__contents[k].Ref__Boolean_value
; [eval] diz.Set__contents[k]
(set-option :timeout 0)
(push) ; 10
(assert (not (not (= ($Seq.index $t@501 k@512) $Ref.null))))
(check-sat)
; unsat
(pop) ; 10
; 0.00s
; (get-info :all-statistics)
(set-option :timeout 0)
(push) ; 10
(assert (not (<
  $Perm.No
  (+
    (+
      (+
        (+
          (+
            (-
              (-
                (ite
                  (and
                    (<= 0 (invOf@121 ($Seq.index $t@501 k@512)))
                    (< (invOf@121 ($Seq.index $t@501 k@512)) $t@116))
                  $Perm.Write
                  $Perm.No)
                ($permsTaken32 ($Seq.index $t@501 k@512)))
              ($permsTaken34 ($Seq.index $t@501 k@512)))
            (-
              (-
                (ite
                  (and
                    (<= 0 (invOf@129 ($Seq.index $t@501 k@512)))
                    (< (invOf@129 ($Seq.index $t@501 k@512)) $t@123))
                  $k@127
                  $Perm.No)
                ($permsTaken31 ($Seq.index $t@501 k@512)))
              ($permsTaken33 ($Seq.index $t@501 k@512))))
          (-
            (-
              (ite
                (and
                  (<= 0 (invOf@386 ($Seq.index $t@501 k@512)))
                  (< (invOf@386 ($Seq.index $t@501 k@512)) $t@382))
                $Perm.Write
                $Perm.No)
              ($permsTaken44 ($Seq.index $t@501 k@512)))
            ($permsTaken48 ($Seq.index $t@501 k@512))))
        (-
          (-
            (ite
              (and
                (<= 0 (invOf@391 ($Seq.index $t@501 k@512)))
                (< (invOf@391 ($Seq.index $t@501 k@512)) $t@375))
              $k@390
              $Perm.No)
            ($permsTaken43 ($Seq.index $t@501 k@512)))
          ($permsTaken47 ($Seq.index $t@501 k@512))))
      (ite
        (and
          (<= 0 (invOf@506 ($Seq.index $t@501 k@512)))
          (< (invOf@506 ($Seq.index $t@501 k@512)) $t@502))
        $Perm.Write
        $Perm.No))
    (ite
      (and
        (<= 0 (invOf@511 ($Seq.index $t@501 k@512)))
        (< (invOf@511 ($Seq.index $t@501 k@512)) $t@495))
      $k@510
      $Perm.No)))))
(check-sat)
; unsat
(pop) ; 10
; 0.17s
; (get-info :all-statistics)
(declare-const fvf@513 $FVF<Bool>)
(assert (forall (($r $Ref)) (!
  (implies
    (and
      (<
        $Perm.No
        (-
          (-
            (ite
              (and (<= 0 (invOf@121 $r)) (< (invOf@121 $r) $t@116))
              $Perm.Write
              $Perm.No)
            ($permsTaken32 $r))
          ($permsTaken34 $r)))
      ($Set.in $r ($FVF.domain_Ref__Boolean_value fvf@513)))
    (=
      ($FVF.lookup_Ref__Boolean_value fvf@513 $r)
      ($FVF.lookup_Ref__Boolean_value $t@120 $r)))
  :pattern (($FVF.lookup_Ref__Boolean_value fvf@513 $r) (invOf@121 $r))
  :pattern (($FVF.lookup_Ref__Boolean_value $t@120 $r) (invOf@121 $r)))))
(assert (forall (($r $Ref)) (!
  (implies
    (and
      (<
        $Perm.No
        (-
          (-
            (ite
              (and (<= 0 (invOf@129 $r)) (< (invOf@129 $r) $t@123))
              $k@127
              $Perm.No)
            ($permsTaken31 $r))
          ($permsTaken33 $r)))
      ($Set.in $r ($FVF.domain_Ref__Boolean_value fvf@513)))
    (=
      ($FVF.lookup_Ref__Boolean_value fvf@513 $r)
      ($FVF.lookup_Ref__Boolean_value $t@128 $r)))
  :pattern (($FVF.lookup_Ref__Boolean_value fvf@513 $r) (invOf@129 $r))
  :pattern (($FVF.lookup_Ref__Boolean_value $t@128 $r) (invOf@129 $r)))))
(assert (forall (($r $Ref)) (!
  (implies
    (and
      (<
        $Perm.No
        (-
          (-
            (ite
              (and (<= 0 (invOf@386 $r)) (< (invOf@386 $r) $t@382))
              $Perm.Write
              $Perm.No)
            ($permsTaken44 $r))
          ($permsTaken48 $r)))
      ($Set.in $r ($FVF.domain_Ref__Boolean_value fvf@513)))
    (=
      ($FVF.lookup_Ref__Boolean_value fvf@513 $r)
      ($FVF.lookup_Ref__Boolean_value $t@378 $r)))
  :pattern (($FVF.lookup_Ref__Boolean_value fvf@513 $r) (invOf@386 $r))
  :pattern (($FVF.lookup_Ref__Boolean_value $t@378 $r) (invOf@386 $r)))))
(assert (forall (($r $Ref)) (!
  (implies
    (and
      (<
        $Perm.No
        (-
          (-
            (ite
              (and (<= 0 (invOf@391 $r)) (< (invOf@391 $r) $t@375))
              $k@390
              $Perm.No)
            ($permsTaken43 $r))
          ($permsTaken47 $r)))
      ($Set.in $r ($FVF.domain_Ref__Boolean_value fvf@513)))
    (=
      ($FVF.lookup_Ref__Boolean_value fvf@513 $r)
      ($FVF.lookup_Ref__Boolean_value $t@368 $r)))
  :pattern (($FVF.lookup_Ref__Boolean_value fvf@513 $r) (invOf@391 $r))
  :pattern (($FVF.lookup_Ref__Boolean_value $t@368 $r) (invOf@391 $r)))))
(assert (forall (($r $Ref)) (!
  (implies
    (and
      (and (<= 0 (invOf@506 $r)) (< (invOf@506 $r) $t@502))
      ($Set.in $r ($FVF.domain_Ref__Boolean_value fvf@513)))
    (=
      ($FVF.lookup_Ref__Boolean_value fvf@513 $r)
      ($FVF.lookup_Ref__Boolean_value $t@498 $r)))
  :pattern (($FVF.lookup_Ref__Boolean_value fvf@513 $r) (invOf@506 $r))
  :pattern (($FVF.lookup_Ref__Boolean_value $t@498 $r) (invOf@506 $r)))))
(assert (forall (($r $Ref)) (!
  (implies
    (and
      (ite
        (and (<= 0 (invOf@511 $r)) (< (invOf@511 $r) $t@495))
        (< $Perm.No $k@510)
        false)
      ($Set.in $r ($FVF.domain_Ref__Boolean_value fvf@513)))
    (=
      ($FVF.lookup_Ref__Boolean_value fvf@513 $r)
      ($FVF.lookup_Ref__Boolean_value $t@488 $r)))
  :pattern (($FVF.lookup_Ref__Boolean_value fvf@513 $r) (invOf@511 $r))
  :pattern (($FVF.lookup_Ref__Boolean_value $t@488 $r) (invOf@511 $r)))))
(assert (forall ((k@512 Int)) (!
  (iff
    ($Set.in ($Seq.index $t@501 k@512) ($FVF.domain_Ref__Boolean_value fvf@513))
    (and (and (>= k@512 $t@495) (< k@512 j@400)) (not (<= $t@116 $t@123))))
  :pattern (($Set.in
    ($Seq.index $t@501 k@512)
    ($FVF.domain_Ref__Boolean_value fvf@513))))))
(pop) ; 9
(push) ; 9
; [else-branch 100] !k@512 >= $t@495 && k@512 < j@400
(assert (not (and (>= k@512 $t@495) (< k@512 j@400))))
(pop) ; 9
(pop) ; 8
(assert (forall ((k@512 Int)) (!
  (iff
    ($Set.in ($Seq.index $t@501 k@512) ($FVF.domain_Ref__Boolean_value fvf@513))
    (and (and (>= k@512 $t@495) (< k@512 j@400)) (not (<= $t@116 $t@123))))
  :pattern (($Set.in
    ($Seq.index $t@501 k@512)
    ($FVF.domain_Ref__Boolean_value fvf@513))))))
(assert (forall (($r $Ref)) (!
  (implies
    (and
      (ite
        (and (<= 0 (invOf@511 $r)) (< (invOf@511 $r) $t@495))
        (< $Perm.No $k@510)
        false)
      ($Set.in $r ($FVF.domain_Ref__Boolean_value fvf@513)))
    (=
      ($FVF.lookup_Ref__Boolean_value fvf@513 $r)
      ($FVF.lookup_Ref__Boolean_value $t@488 $r)))
  :pattern (($FVF.lookup_Ref__Boolean_value fvf@513 $r) (invOf@511 $r))
  :pattern (($FVF.lookup_Ref__Boolean_value $t@488 $r) (invOf@511 $r)))))
(assert (forall (($r $Ref)) (!
  (implies
    (and
      (and (<= 0 (invOf@506 $r)) (< (invOf@506 $r) $t@502))
      ($Set.in $r ($FVF.domain_Ref__Boolean_value fvf@513)))
    (=
      ($FVF.lookup_Ref__Boolean_value fvf@513 $r)
      ($FVF.lookup_Ref__Boolean_value $t@498 $r)))
  :pattern (($FVF.lookup_Ref__Boolean_value fvf@513 $r) (invOf@506 $r))
  :pattern (($FVF.lookup_Ref__Boolean_value $t@498 $r) (invOf@506 $r)))))
(assert (forall (($r $Ref)) (!
  (implies
    (and
      (<
        $Perm.No
        (-
          (-
            (ite
              (and (<= 0 (invOf@391 $r)) (< (invOf@391 $r) $t@375))
              $k@390
              $Perm.No)
            ($permsTaken43 $r))
          ($permsTaken47 $r)))
      ($Set.in $r ($FVF.domain_Ref__Boolean_value fvf@513)))
    (=
      ($FVF.lookup_Ref__Boolean_value fvf@513 $r)
      ($FVF.lookup_Ref__Boolean_value $t@368 $r)))
  :pattern (($FVF.lookup_Ref__Boolean_value fvf@513 $r) (invOf@391 $r))
  :pattern (($FVF.lookup_Ref__Boolean_value $t@368 $r) (invOf@391 $r)))))
(assert (forall (($r $Ref)) (!
  (implies
    (and
      (<
        $Perm.No
        (-
          (-
            (ite
              (and (<= 0 (invOf@386 $r)) (< (invOf@386 $r) $t@382))
              $Perm.Write
              $Perm.No)
            ($permsTaken44 $r))
          ($permsTaken48 $r)))
      ($Set.in $r ($FVF.domain_Ref__Boolean_value fvf@513)))
    (=
      ($FVF.lookup_Ref__Boolean_value fvf@513 $r)
      ($FVF.lookup_Ref__Boolean_value $t@378 $r)))
  :pattern (($FVF.lookup_Ref__Boolean_value fvf@513 $r) (invOf@386 $r))
  :pattern (($FVF.lookup_Ref__Boolean_value $t@378 $r) (invOf@386 $r)))))
(assert (forall (($r $Ref)) (!
  (implies
    (and
      (<
        $Perm.No
        (-
          (-
            (ite
              (and (<= 0 (invOf@129 $r)) (< (invOf@129 $r) $t@123))
              $k@127
              $Perm.No)
            ($permsTaken31 $r))
          ($permsTaken33 $r)))
      ($Set.in $r ($FVF.domain_Ref__Boolean_value fvf@513)))
    (=
      ($FVF.lookup_Ref__Boolean_value fvf@513 $r)
      ($FVF.lookup_Ref__Boolean_value $t@128 $r)))
  :pattern (($FVF.lookup_Ref__Boolean_value fvf@513 $r) (invOf@129 $r))
  :pattern (($FVF.lookup_Ref__Boolean_value $t@128 $r) (invOf@129 $r)))))
(assert (forall (($r $Ref)) (!
  (implies
    (and
      (<
        $Perm.No
        (-
          (-
            (ite
              (and (<= 0 (invOf@121 $r)) (< (invOf@121 $r) $t@116))
              $Perm.Write
              $Perm.No)
            ($permsTaken32 $r))
          ($permsTaken34 $r)))
      ($Set.in $r ($FVF.domain_Ref__Boolean_value fvf@513)))
    (=
      ($FVF.lookup_Ref__Boolean_value fvf@513 $r)
      ($FVF.lookup_Ref__Boolean_value $t@120 $r)))
  :pattern (($FVF.lookup_Ref__Boolean_value fvf@513 $r) (invOf@121 $r))
  :pattern (($FVF.lookup_Ref__Boolean_value $t@120 $r) (invOf@121 $r)))))
(pop) ; 7
(assert (forall ((k@512 Int)) (!
  (iff
    ($Set.in ($Seq.index $t@501 k@512) ($FVF.domain_Ref__Boolean_value fvf@513))
    (and (and (>= k@512 $t@495) (< k@512 j@400)) (not (<= $t@116 $t@123))))
  :pattern (($Set.in
    ($Seq.index $t@501 k@512)
    ($FVF.domain_Ref__Boolean_value fvf@513))))))
(assert (forall (($r $Ref)) (!
  (implies
    (and
      (ite
        (and (<= 0 (invOf@511 $r)) (< (invOf@511 $r) $t@495))
        (< $Perm.No $k@510)
        false)
      ($Set.in $r ($FVF.domain_Ref__Boolean_value fvf@513)))
    (=
      ($FVF.lookup_Ref__Boolean_value fvf@513 $r)
      ($FVF.lookup_Ref__Boolean_value $t@488 $r)))
  :pattern (($FVF.lookup_Ref__Boolean_value fvf@513 $r) (invOf@511 $r))
  :pattern (($FVF.lookup_Ref__Boolean_value $t@488 $r) (invOf@511 $r)))))
(assert (forall (($r $Ref)) (!
  (implies
    (and
      (and (<= 0 (invOf@506 $r)) (< (invOf@506 $r) $t@502))
      ($Set.in $r ($FVF.domain_Ref__Boolean_value fvf@513)))
    (=
      ($FVF.lookup_Ref__Boolean_value fvf@513 $r)
      ($FVF.lookup_Ref__Boolean_value $t@498 $r)))
  :pattern (($FVF.lookup_Ref__Boolean_value fvf@513 $r) (invOf@506 $r))
  :pattern (($FVF.lookup_Ref__Boolean_value $t@498 $r) (invOf@506 $r)))))
(assert (forall (($r $Ref)) (!
  (implies
    (and
      (<
        $Perm.No
        (-
          (-
            (ite
              (and (<= 0 (invOf@391 $r)) (< (invOf@391 $r) $t@375))
              $k@390
              $Perm.No)
            ($permsTaken43 $r))
          ($permsTaken47 $r)))
      ($Set.in $r ($FVF.domain_Ref__Boolean_value fvf@513)))
    (=
      ($FVF.lookup_Ref__Boolean_value fvf@513 $r)
      ($FVF.lookup_Ref__Boolean_value $t@368 $r)))
  :pattern (($FVF.lookup_Ref__Boolean_value fvf@513 $r) (invOf@391 $r))
  :pattern (($FVF.lookup_Ref__Boolean_value $t@368 $r) (invOf@391 $r)))))
(assert (forall (($r $Ref)) (!
  (implies
    (and
      (<
        $Perm.No
        (-
          (-
            (ite
              (and (<= 0 (invOf@386 $r)) (< (invOf@386 $r) $t@382))
              $Perm.Write
              $Perm.No)
            ($permsTaken44 $r))
          ($permsTaken48 $r)))
      ($Set.in $r ($FVF.domain_Ref__Boolean_value fvf@513)))
    (=
      ($FVF.lookup_Ref__Boolean_value fvf@513 $r)
      ($FVF.lookup_Ref__Boolean_value $t@378 $r)))
  :pattern (($FVF.lookup_Ref__Boolean_value fvf@513 $r) (invOf@386 $r))
  :pattern (($FVF.lookup_Ref__Boolean_value $t@378 $r) (invOf@386 $r)))))
(assert (forall (($r $Ref)) (!
  (implies
    (and
      (<
        $Perm.No
        (-
          (-
            (ite
              (and (<= 0 (invOf@129 $r)) (< (invOf@129 $r) $t@123))
              $k@127
              $Perm.No)
            ($permsTaken31 $r))
          ($permsTaken33 $r)))
      ($Set.in $r ($FVF.domain_Ref__Boolean_value fvf@513)))
    (=
      ($FVF.lookup_Ref__Boolean_value fvf@513 $r)
      ($FVF.lookup_Ref__Boolean_value $t@128 $r)))
  :pattern (($FVF.lookup_Ref__Boolean_value fvf@513 $r) (invOf@129 $r))
  :pattern (($FVF.lookup_Ref__Boolean_value $t@128 $r) (invOf@129 $r)))))
(assert (forall (($r $Ref)) (!
  (implies
    (and
      (<
        $Perm.No
        (-
          (-
            (ite
              (and (<= 0 (invOf@121 $r)) (< (invOf@121 $r) $t@116))
              $Perm.Write
              $Perm.No)
            ($permsTaken32 $r))
          ($permsTaken34 $r)))
      ($Set.in $r ($FVF.domain_Ref__Boolean_value fvf@513)))
    (=
      ($FVF.lookup_Ref__Boolean_value fvf@513 $r)
      ($FVF.lookup_Ref__Boolean_value $t@120 $r)))
  :pattern (($FVF.lookup_Ref__Boolean_value fvf@513 $r) (invOf@121 $r))
  :pattern (($FVF.lookup_Ref__Boolean_value $t@120 $r) (invOf@121 $r)))))
(assert (forall ((k@512 Int)) (!
  (implies
    (and (>= k@512 $t@495) (< k@512 j@400))
    (not ($FVF.lookup_Ref__Boolean_value fvf@513 ($Seq.index $t@501 k@512))))
  :pattern (($Seq.index $t@501 k@512)))))
; [eval] !(j < diz.Set__max)
; [eval] j < diz.Set__max
(assert (not (< j@400 $t@502)))
(set-option :timeout 0)
(check-sat)
; unknown
(declare-const $k@514 $Perm)
(assert ($Perm.isValidVar $k@514))
(assert ($Perm.isReadVar $k@514 $Perm.Write))
(set-option :timeout 0)
(push) ; 7
(assert (not (or (= $k@514 $Perm.No) true)))
(check-sat)
; unsat
(pop) ; 7
; 0.00s
; (get-info :all-statistics)
(assert (< $k@514 (+ (- (+ (- $k@115 $k@340) $k@383) $k@460) $k@503)))
; [eval] diz.Set__max > 0
(declare-const $k@515 $Perm)
(assert ($Perm.isValidVar $k@515))
(assert ($Perm.isReadVar $k@515 $Perm.Write))
(set-option :timeout 0)
(push) ; 7
(assert (not (or (= $k@515 $Perm.No) true)))
(check-sat)
; unsat
(pop) ; 7
; 0.00s
; (get-info :all-statistics)
(assert (< $k@515 (+ (- (+ (- $k@117 $k@341) $k@384) $k@461) $k@504)))
; [eval] |diz.Set__contents| == diz.Set__max
; [eval] |diz.Set__contents|
(declare-const fvf@516 $FVF<Int>)
(declare-const fvf@517 $FVF<Int>)
(declare-const fvf@518 $FVF<$Seq<$Ref>>)
(declare-const fvf@519 $FVF<$Seq<$Ref>>)
(assert (= ($FVF.lookup_Set__max fvf@516 diz@101) $t@502))
(assert ($Set.equal ($FVF.domain_Set__max fvf@516) ($Set.singleton  diz@101)))
(assert (= ($FVF.lookup_Set__max fvf@517 x@102) $t@495))
(assert ($Set.equal ($FVF.domain_Set__max fvf@517) ($Set.singleton  x@102)))
(assert ($Seq.equal ($FVF.lookup_Set__contents fvf@518 diz@101) $t@501))
(assert ($Set.equal ($FVF.domain_Set__contents fvf@518) ($Set.singleton  diz@101)))
(assert ($Seq.equal ($FVF.lookup_Set__contents fvf@519 x@102) $t@492))
(assert ($Set.equal ($FVF.domain_Set__contents fvf@519) ($Set.singleton  x@102)))
(declare-const k@520 Int)
; [eval] (0 <= k) && (k < diz.Set__max)
; [eval] 0 <= k
(push) ; 7
(set-option :timeout 0)
(push) ; 8
(assert (not (not (<= 0 k@520))))
(check-sat)
; unknown
(pop) ; 8
; 0.01s
; (get-info :all-statistics)
(set-option :timeout 0)
(push) ; 8
(assert (not (<= 0 k@520)))
(check-sat)
; unknown
(pop) ; 8
; 0.01s
; (get-info :all-statistics)
(push) ; 8
; [then-branch 101] 0 <= k@520
(assert (<= 0 k@520))
; [eval] k < diz.Set__max
(set-option :timeout 0)
(push) ; 9
(assert (not (<
  $Perm.No
  (+
    (+ (- (+ (- $k@115 $k@340) $k@383) $k@460) $k@503)
    (ite
      (= diz@101 x@102)
      (+ (- (+ (- $k@122 $k@351) $k@387) $k@471) $k@507)
      $Perm.No)))))
(check-sat)
; unsat
(pop) ; 9
; 0.00s
; (get-info :all-statistics)
(declare-const fvf@521 $FVF<Int>)
(assert (implies
  (< $Perm.No (+ (- (+ (- $k@115 $k@340) $k@383) $k@460) $k@503))
  (=
    ($FVF.lookup_Set__max fvf@521 diz@101)
    ($FVF.lookup_Set__max fvf@516 diz@101))))
(assert (implies
  (ite
    (= diz@101 x@102)
    (< $Perm.No (+ (- (+ (- $k@122 $k@351) $k@387) $k@471) $k@507))
    false)
  (=
    ($FVF.lookup_Set__max fvf@521 diz@101)
    ($FVF.lookup_Set__max fvf@517 diz@101))))
(assert ($Set.equal ($FVF.domain_Set__max fvf@521) ($Set.singleton  diz@101)))
(pop) ; 8
(push) ; 8
; [else-branch 101] !0 <= k@520
(assert (not (<= 0 k@520)))
(pop) ; 8
(pop) ; 7
(assert ($Set.equal ($FVF.domain_Set__max fvf@521) ($Set.singleton  diz@101)))
(assert (implies
  (ite
    (= diz@101 x@102)
    (< $Perm.No (+ (- (+ (- $k@122 $k@351) $k@387) $k@471) $k@507))
    false)
  (=
    ($FVF.lookup_Set__max fvf@521 diz@101)
    ($FVF.lookup_Set__max fvf@517 diz@101))))
(assert (implies
  (< $Perm.No (+ (- (+ (- $k@115 $k@340) $k@383) $k@460) $k@503))
  (=
    ($FVF.lookup_Set__max fvf@521 diz@101)
    ($FVF.lookup_Set__max fvf@516 diz@101))))
(set-option :timeout 0)
(push) ; 7
(assert (not (not (and (<= 0 k@520) (< k@520 ($FVF.lookup_Set__max fvf@521 diz@101))))))
(check-sat)
; unknown
(pop) ; 7
; 0.01s
; (get-info :all-statistics)
(assert (and (<= 0 k@520) (< k@520 ($FVF.lookup_Set__max fvf@521 diz@101))))
; [eval] diz.Set__contents[k]
(set-option :timeout 0)
(push) ; 7
(assert (not (<
  $Perm.No
  (+
    (+ (- (+ (- $k@117 $k@341) $k@384) $k@461) $k@504)
    (ite
      (= diz@101 x@102)
      (+ (- (+ (- $k@124 $k@352) $k@388) $k@472) $k@508)
      $Perm.No)))))
(check-sat)
; unsat
(pop) ; 7
; 0.00s
; (get-info :all-statistics)
(declare-const fvf@522 $FVF<$Seq<$Ref>>)
(assert (implies
  (< $Perm.No (+ (- (+ (- $k@117 $k@341) $k@384) $k@461) $k@504))
  ($Seq.equal
    ($FVF.lookup_Set__contents fvf@522 diz@101)
    ($FVF.lookup_Set__contents fvf@518 diz@101))))
(assert (implies
  (ite
    (= diz@101 x@102)
    (< $Perm.No (+ (- (+ (- $k@124 $k@352) $k@388) $k@472) $k@508))
    false)
  ($Seq.equal
    ($FVF.lookup_Set__contents fvf@522 diz@101)
    ($FVF.lookup_Set__contents fvf@519 diz@101))))
(assert ($Set.equal ($FVF.domain_Set__contents fvf@522) ($Set.singleton  diz@101)))
(set-option :timeout 0)
(push) ; 7
(assert (not (forall (($x Int) ($y Int)) (!
  (implies
    (and
      (and (<= 0 $x) (< $x ($FVF.lookup_Set__max fvf@521 diz@101)))
      (and (<= 0 $y) (< $y ($FVF.lookup_Set__max fvf@521 diz@101)))
      (=
        ($Seq.index ($FVF.lookup_Set__contents fvf@522 diz@101) $x)
        ($Seq.index ($FVF.lookup_Set__contents fvf@522 diz@101) $y)))
    (= $x $y))
  :pattern (($Seq.index ($FVF.lookup_Set__contents fvf@522 diz@101) $x) ($Seq.index
    ($FVF.lookup_Set__contents fvf@522 diz@101)
    $y))))))
(check-sat)
; unsat
(pop) ; 7
; 0.01s
; (get-info :all-statistics)
(declare-fun invOf@523 ($Ref) Int)
(assert (forall (($r $Ref)) (!
  (implies
    (and
      (<= 0 (invOf@523 $r))
      (< (invOf@523 $r) ($FVF.lookup_Set__max fvf@521 diz@101)))
    (=
      ($Seq.index ($FVF.lookup_Set__contents fvf@522 diz@101) (invOf@523 $r))
      $r))
  :pattern ((invOf@523 $r)))))
(assert (forall ((k@520 Int)) (!
  (implies
    (and (<= 0 k@520) (< k@520 ($FVF.lookup_Set__max fvf@521 diz@101)))
    (=
      (invOf@523 ($Seq.index ($FVF.lookup_Set__contents fvf@522 diz@101) k@520))
      k@520))
  :pattern (($Seq.index ($FVF.lookup_Set__contents fvf@522 diz@101) k@520)))))
(declare-const fvf@524 $FVF<Bool>)
; Precomputing split data for Lookup(Set__contents,fvf@522,diz@101)[k@520].Ref__Boolean_value # W
(define-fun $permsTaken51 (($r $Ref)) $Perm
  ($Perm.min
    (ite
      (and
        (<= 0 (invOf@523 $r))
        (< (invOf@523 $r) ($FVF.lookup_Set__max fvf@521 diz@101)))
      $Perm.Write
      $Perm.No)
    (ite
      (= $r ($Seq.index ($FVF.lookup_Set__contents fvf@522 diz@101) k@520))
      (ite (and (<= 0 (invOf@511 $r)) (< (invOf@511 $r) $t@495)) $k@510 $Perm.No)
      $Perm.No)))
(define-fun $permsTaken52 (($r $Ref)) $Perm
  ($Perm.min
    (-
      (ite
        (and
          (<= 0 (invOf@523 $r))
          (< (invOf@523 $r) ($FVF.lookup_Set__max fvf@521 diz@101)))
        $Perm.Write
        $Perm.No)
      ($permsTaken51 $r))
    (ite
      (= $r ($Seq.index ($FVF.lookup_Set__contents fvf@522 diz@101) k@520))
      (ite
        (and (<= 0 (invOf@506 $r)) (< (invOf@506 $r) $t@502))
        $Perm.Write
        $Perm.No)
      $Perm.No)))
(define-fun $permsTaken53 (($r $Ref)) $Perm
  ($Perm.min
    (-
      (-
        (ite
          (and
            (<= 0 (invOf@523 $r))
            (< (invOf@523 $r) ($FVF.lookup_Set__max fvf@521 diz@101)))
          $Perm.Write
          $Perm.No)
        ($permsTaken51 $r))
      ($permsTaken52 $r))
    (ite
      (= $r ($Seq.index ($FVF.lookup_Set__contents fvf@522 diz@101) k@520))
      (-
        (-
          (ite
            (and (<= 0 (invOf@391 $r)) (< (invOf@391 $r) $t@375))
            $k@390
            $Perm.No)
          ($permsTaken43 $r))
        ($permsTaken47 $r))
      $Perm.No)))
(define-fun $permsTaken54 (($r $Ref)) $Perm
  ($Perm.min
    (-
      (-
        (-
          (ite
            (and
              (<= 0 (invOf@523 $r))
              (< (invOf@523 $r) ($FVF.lookup_Set__max fvf@521 diz@101)))
            $Perm.Write
            $Perm.No)
          ($permsTaken51 $r))
        ($permsTaken52 $r))
      ($permsTaken53 $r))
    (ite
      (= $r ($Seq.index ($FVF.lookup_Set__contents fvf@522 diz@101) k@520))
      (-
        (-
          (ite
            (and (<= 0 (invOf@386 $r)) (< (invOf@386 $r) $t@382))
            $Perm.Write
            $Perm.No)
          ($permsTaken44 $r))
        ($permsTaken48 $r))
      $Perm.No)))
(define-fun $permsTaken55 (($r $Ref)) $Perm
  ($Perm.min
    (-
      (-
        (-
          (-
            (ite
              (and
                (<= 0 (invOf@523 $r))
                (< (invOf@523 $r) ($FVF.lookup_Set__max fvf@521 diz@101)))
              $Perm.Write
              $Perm.No)
            ($permsTaken51 $r))
          ($permsTaken52 $r))
        ($permsTaken53 $r))
      ($permsTaken54 $r))
    (ite
      (= $r ($Seq.index ($FVF.lookup_Set__contents fvf@522 diz@101) k@520))
      (-
        (-
          (ite
            (and (<= 0 (invOf@129 $r)) (< (invOf@129 $r) $t@123))
            $k@127
            $Perm.No)
          ($permsTaken31 $r))
        ($permsTaken33 $r))
      $Perm.No)))
(define-fun $permsTaken56 (($r $Ref)) $Perm
  ($Perm.min
    (-
      (-
        (-
          (-
            (-
              (ite
                (and
                  (<= 0 (invOf@523 $r))
                  (< (invOf@523 $r) ($FVF.lookup_Set__max fvf@521 diz@101)))
                $Perm.Write
                $Perm.No)
              ($permsTaken51 $r))
            ($permsTaken52 $r))
          ($permsTaken53 $r))
        ($permsTaken54 $r))
      ($permsTaken55 $r))
    (ite
      (= $r ($Seq.index ($FVF.lookup_Set__contents fvf@522 diz@101) k@520))
      (-
        (-
          (ite
            (and (<= 0 (invOf@121 $r)) (< (invOf@121 $r) $t@116))
            $Perm.Write
            $Perm.No)
          ($permsTaken32 $r))
        ($permsTaken34 $r))
      $Perm.No)))
; Done precomputing, updating quantified heap chunks
; Chunk depleted?
(set-option :timeout 500)
(push) ; 7
(assert (not (forall (($r $Ref)) (!
  (=
    (-
      (ite (and (<= 0 (invOf@511 $r)) (< (invOf@511 $r) $t@495)) $k@510 $Perm.No)
      ($permsTaken51 $r))
    $Perm.No)
  ))))
(check-sat)
; unknown
(pop) ; 7
; 0.50s
; (get-info :all-statistics)
; Enough permissions taken?
(set-option :timeout 500)
(push) ; 7
(assert (not (=
  (-
    (ite
      (and
        (<=
          0
          (invOf@523 ($Seq.index
            ($FVF.lookup_Set__contents fvf@522 diz@101)
            k@520)))
        (<
          (invOf@523 ($Seq.index
            ($FVF.lookup_Set__contents fvf@522 diz@101)
            k@520))
          ($FVF.lookup_Set__max fvf@521 diz@101)))
      $Perm.Write
      $Perm.No)
    ($permsTaken51 ($Seq.index ($FVF.lookup_Set__contents fvf@522 diz@101) k@520)))
  $Perm.No)))
(check-sat)
; unknown
(pop) ; 7
; 0.47s
; (get-info :all-statistics)
; Chunk depleted?
(set-option :timeout 500)
(push) ; 7
(assert (not (forall (($r $Ref)) (!
  (=
    (-
      (ite
        (and (<= 0 (invOf@506 $r)) (< (invOf@506 $r) $t@502))
        $Perm.Write
        $Perm.No)
      ($permsTaken52 $r))
    $Perm.No)
  ))))
(check-sat)
; unknown
(pop) ; 7
; 0.50s
; (get-info :all-statistics)
; Enough permissions taken?
(set-option :timeout 500)
(push) ; 7
(assert (not (=
  (-
    (-
      (ite
        (and
          (<=
            0
            (invOf@523 ($Seq.index
              ($FVF.lookup_Set__contents fvf@522 diz@101)
              k@520)))
          (<
            (invOf@523 ($Seq.index
              ($FVF.lookup_Set__contents fvf@522 diz@101)
              k@520))
            ($FVF.lookup_Set__max fvf@521 diz@101)))
        $Perm.Write
        $Perm.No)
      ($permsTaken51 ($Seq.index
        ($FVF.lookup_Set__contents fvf@522 diz@101)
        k@520)))
    ($permsTaken52 ($Seq.index ($FVF.lookup_Set__contents fvf@522 diz@101) k@520)))
  $Perm.No)))
(check-sat)
; unsat
(pop) ; 7
; 0.02s
; (get-info :all-statistics)
; Final check that enough permissions have been taken
; Done splitting
(assert (forall (($r $Ref)) (!
  (implies
    (and
      (<
        $Perm.No
        (-
          (-
            (ite
              (and (<= 0 (invOf@121 $r)) (< (invOf@121 $r) $t@116))
              $Perm.Write
              $Perm.No)
            ($permsTaken32 $r))
          ($permsTaken34 $r)))
      ($Set.in $r ($FVF.domain_Ref__Boolean_value fvf@524)))
    (=
      ($FVF.lookup_Ref__Boolean_value fvf@524 $r)
      ($FVF.lookup_Ref__Boolean_value $t@120 $r)))
  :pattern (($FVF.lookup_Ref__Boolean_value fvf@524 $r) (invOf@121 $r))
  :pattern (($FVF.lookup_Ref__Boolean_value $t@120 $r) (invOf@121 $r)))))
(assert (forall (($r $Ref)) (!
  (implies
    (and
      (<
        $Perm.No
        (-
          (-
            (ite
              (and (<= 0 (invOf@129 $r)) (< (invOf@129 $r) $t@123))
              $k@127
              $Perm.No)
            ($permsTaken31 $r))
          ($permsTaken33 $r)))
      ($Set.in $r ($FVF.domain_Ref__Boolean_value fvf@524)))
    (=
      ($FVF.lookup_Ref__Boolean_value fvf@524 $r)
      ($FVF.lookup_Ref__Boolean_value $t@128 $r)))
  :pattern (($FVF.lookup_Ref__Boolean_value fvf@524 $r) (invOf@129 $r))
  :pattern (($FVF.lookup_Ref__Boolean_value $t@128 $r) (invOf@129 $r)))))
(assert (forall (($r $Ref)) (!
  (implies
    (and
      (<
        $Perm.No
        (-
          (-
            (ite
              (and (<= 0 (invOf@386 $r)) (< (invOf@386 $r) $t@382))
              $Perm.Write
              $Perm.No)
            ($permsTaken44 $r))
          ($permsTaken48 $r)))
      ($Set.in $r ($FVF.domain_Ref__Boolean_value fvf@524)))
    (=
      ($FVF.lookup_Ref__Boolean_value fvf@524 $r)
      ($FVF.lookup_Ref__Boolean_value $t@378 $r)))
  :pattern (($FVF.lookup_Ref__Boolean_value fvf@524 $r) (invOf@386 $r))
  :pattern (($FVF.lookup_Ref__Boolean_value $t@378 $r) (invOf@386 $r)))))
(assert (forall (($r $Ref)) (!
  (implies
    (and
      (<
        $Perm.No
        (-
          (-
            (ite
              (and (<= 0 (invOf@391 $r)) (< (invOf@391 $r) $t@375))
              $k@390
              $Perm.No)
            ($permsTaken43 $r))
          ($permsTaken47 $r)))
      ($Set.in $r ($FVF.domain_Ref__Boolean_value fvf@524)))
    (=
      ($FVF.lookup_Ref__Boolean_value fvf@524 $r)
      ($FVF.lookup_Ref__Boolean_value $t@368 $r)))
  :pattern (($FVF.lookup_Ref__Boolean_value fvf@524 $r) (invOf@391 $r))
  :pattern (($FVF.lookup_Ref__Boolean_value $t@368 $r) (invOf@391 $r)))))
(assert (forall (($r $Ref)) (!
  (implies
    (and
      (and (<= 0 (invOf@506 $r)) (< (invOf@506 $r) $t@502))
      ($Set.in $r ($FVF.domain_Ref__Boolean_value fvf@524)))
    (=
      ($FVF.lookup_Ref__Boolean_value fvf@524 $r)
      ($FVF.lookup_Ref__Boolean_value $t@498 $r)))
  :pattern (($FVF.lookup_Ref__Boolean_value fvf@524 $r) (invOf@506 $r))
  :pattern (($FVF.lookup_Ref__Boolean_value $t@498 $r) (invOf@506 $r)))))
(assert (forall (($r $Ref)) (!
  (implies
    (and
      (ite
        (and (<= 0 (invOf@511 $r)) (< (invOf@511 $r) $t@495))
        (< $Perm.No $k@510)
        false)
      ($Set.in $r ($FVF.domain_Ref__Boolean_value fvf@524)))
    (=
      ($FVF.lookup_Ref__Boolean_value fvf@524 $r)
      ($FVF.lookup_Ref__Boolean_value $t@488 $r)))
  :pattern (($FVF.lookup_Ref__Boolean_value fvf@524 $r) (invOf@511 $r))
  :pattern (($FVF.lookup_Ref__Boolean_value $t@488 $r) (invOf@511 $r)))))
(assert (forall (($r $Ref)) (!
  (iff
    ($Set.in $r ($FVF.domain_Ref__Boolean_value fvf@524))
    (and
      (<= 0 (invOf@523 $r))
      (< (invOf@523 $r) ($FVF.lookup_Set__max fvf@521 diz@101))))
  :pattern (($Set.in $r ($FVF.domain_Ref__Boolean_value fvf@524))))))
(pop) ; 6
(pop) ; 5
(pop) ; 4
(push) ; 4
; [else-branch 53] $t@116 <= $t@123
(assert (<= $t@116 $t@123))
(pop) ; 4
(pop) ; 3
(pop) ; 2
; ---------- Set__new_array_Boolean ----------
(declare-const diz@525 $Ref)
(declare-const len@526 Int)
(declare-const sys__result@527 $Seq<$Ref>)
(push) ; 2
; [eval] diz != null
(assert (not (= diz@525 $Ref.null)))
(push) ; 3
; [eval] |sys__result| == len
; [eval] |sys__result|
(assert (= ($Seq.length sys__result@527) len@526))
(declare-const i@528 Int)
(push) ; 4
; [eval] (0 <= i) && (i < |sys__result|)
; [eval] 0 <= i
(push) ; 5
(set-option :timeout 0)
(push) ; 6
(assert (not (not (<= 0 i@528))))
(check-sat)
; unknown
(pop) ; 6
; 0.00s
; (get-info :all-statistics)
(set-option :timeout 0)
(push) ; 6
(assert (not (<= 0 i@528)))
(check-sat)
; unknown
(pop) ; 6
; 0.00s
; (get-info :all-statistics)
(push) ; 6
; [then-branch 102] 0 <= i@528
(assert (<= 0 i@528))
; [eval] i < |sys__result|
; [eval] |sys__result|
(pop) ; 6
(push) ; 6
; [else-branch 102] !0 <= i@528
(assert (not (<= 0 i@528)))
(pop) ; 6
(pop) ; 5
(assert (and (<= 0 i@528) (< i@528 ($Seq.length sys__result@527))))
; [eval] sys__result[i]
(pop) ; 4
(declare-const $t@529 $FVF<Bool>)
(declare-fun invOf@530 ($Ref) Int)
(assert (forall (($r $Ref)) (!
  (implies
    (and (<= 0 (invOf@530 $r)) (< (invOf@530 $r) ($Seq.length sys__result@527)))
    (= ($Seq.index sys__result@527 (invOf@530 $r)) $r))
  :pattern ((invOf@530 $r)))))
(assert (forall ((i@528 Int)) (!
  (implies
    (and (<= 0 i@528) (< i@528 ($Seq.length sys__result@527)))
    (= (invOf@530 ($Seq.index sys__result@527 i@528)) i@528))
  :pattern (($Seq.index sys__result@527 i@528)))))
(assert (forall ((i@528 Int)) (!
  (iff
    ($Set.in
      ($Seq.index sys__result@527 i@528)
      ($FVF.domain_Ref__Boolean_value $t@529))
    (and (<= 0 i@528) (< i@528 ($Seq.length sys__result@527))))
  :pattern (($Set.in
    ($Seq.index sys__result@527 i@528)
    ($FVF.domain_Ref__Boolean_value $t@529))))))
(assert (forall ((i@528 Int)) (!
  (implies
    (and (<= 0 i@528) (< i@528 ($Seq.length sys__result@527)))
    (not (= ($Seq.index sys__result@527 i@528) $Ref.null)))
  :pattern (($Seq.index sys__result@527 i@528)))))
(pop) ; 3
(push) ; 3
; [exec]
; inhale false
(pop) ; 3
(pop) ; 2
