import LeanJavaScripty.Semantics
import LeanJavaScripty.Syntax

-- Abstract Addresses (e.g., "Alloc_Line10")
abbrev Addr := String

inductive Bound where
  | ninf : Bound          -- Negative Infinity
  | pinf : Bound          -- Positive Infinity
  | val  : Int → Bound    -- Concrete Integer Value
deriving Repr, DecidableEq, Inhabited

def Bound.min : Bound → Bound → Bound
  | .pinf, b => b
  | b, .pinf => b
  | .ninf, _ => .ninf
  | _, .ninf => .ninf
  | .val v1, .val v2 => .val (if v1 < v2 then v1 else v2)

def Bound.max : Bound → Bound → Bound
  | .pinf, _ => .pinf
  | _, .pinf => .pinf
  | .ninf, b => b
  | b, .ninf => b
  | .val v1, .val v2 => .val (if v1 > v2 then v1 else v2)

def Bound.add : Bound → Bound → Bound
  | .ninf, _ => .ninf
  | _, .ninf => .ninf
  | .pinf, _ => .pinf
  | _, .pinf => .pinf
  | .val v1, .val v2 => .val (v1 + v2)

def Bound.sub : Bound → Bound → Bound
  | .ninf, _ => .ninf
  | _, .ninf => .ninf
  | .pinf, _ => .pinf
  | _, .pinf => .pinf
  | .val v1, .val v2 => .val (v1 - v2)

instance: LE Bound where
  le b1 b2 := match b1, b2 with
    | .ninf, _ => true
    | _, .pinf => true
    | .pinf, _ => false
    | _, .ninf => false
    | .val v1, .val v2 => v1 ≤ v2

instance: LT Bound where
  lt b1 b2 := match b1, b2 with
    | .ninf, .ninf => false
    | .ninf, _ => true
    | _, .ninf => false
    | _, .pinf => true
    | .pinf, _ => false
    | .val v1, .val v2 => v1 < v2

def Bound.lt_decidable (b1 b2 : Bound) : Bool := match b1, b2 with
  | .ninf, .ninf => false
  | .ninf, _ => true
  | _, .ninf => false
  | _, .pinf => true
  | .pinf, _ => false
  | .val v1, .val v2 => v1 < v2


def Bound.eq_decidable (b1 b2 : Bound) : Bool := match b1, b2 with
  | .ninf, .ninf => true
  | .pinf, .pinf => true
  | .val v1, .val v2 => v1 == v2
  | _, _ => false

def Bound.gt_decidable (b1 b2 : Bound) : Bool := Bound.lt_decidable b2 b1

-- instance: Decidable (b1 < b2) where
--   decide := match b1, b2 with
--     | .ninf, .ninf => isFalse (by decide)
--     | .ninf, _ => isTrue (by decide)
--     | _, .ninf => isFalse (by decide)
--     | _, .pinf => isTrue (by decide)
--     | .pinf, _ => isFalse (by decide)
--     | .val v1, .val v2 => decidable_of_iff (v1 < v2) Iff.rfl


inductive Interval where
  | bottom : Interval                         -- Empty Interval
  | range : Bound → Bound → Interval       -- [lower, upper]
deriving Repr, DecidableEq, Inhabited

def Interval.add (i1 i2: Interval) : Interval := match i1, i2 with
  | .bottom, _ => .bottom
  | _, .bottom => .bottom
  | .range l1 u1, .range l2 u2 => .range (Bound.add l1 l2) (Bound.add u1 u2)

def Interval.sub (i1 i2: Interval) : Interval := match i1, i2 with
  | .bottom, _ => .bottom
  | _, .bottom => .bottom
  | .range l1 u1, .range l2 u2 => .range (Bound.sub l1 l2) (Bound.sub u1 u2)

-- Join using proper min/max semantics (no widening) - this is the standard lattice join
def Interval.join (i1 i2: Interval) : Interval := match i1, i2 with
  | .bottom, i => i
  | i, .bottom => i
  | .range l1 u1, .range l2 u2 =>
    .range (Bound.min l1 l2) (Bound.max u1 u2)

-- Alias for backwards compatibility
def Interval.pureJoin (i1 i2: Interval) : Interval := Interval.join i1 i2



def Interval.widen (oldVal newVal : Interval) : Interval := match oldVal, newVal with
  | .bottom, i => i
  | i, .bottom => i
  | .range l1 u1, .range l2 u2 =>
      let newLb := if Bound.lt_decidable l2 l1 then Bound.ninf else l1 -- If dropping, go to -∞
      let newUb := if Bound.gt_decidable u2 u1 then Bound.pinf else u1 -- If growing, go to +∞
      .range newLb newUb

-- Equality check for intervals
def Interval.eq_decidable (i1 i2 : Interval) : Bool := match i1, i2 with
  | .bottom, .bottom => true
  | .range l1 u1, .range l2 u2 => Bound.eq_decidable l1 l2 && Bound.eq_decidable u1 u2
  | _, _ => false

inductive AbsBool where
  | bottom : AbsBool
  | top : AbsBool
  | bool : Bool → AbsBool
deriving Repr, DecidableEq, Inhabited

def AbsBool.join (b1 b2 : AbsBool) : AbsBool := match b1, b2 with
  | .bottom, b => b
  | b, .bottom => b
  | .bool v1, .bool v2 => if (v1 == v2) then .bool v1 else .top
  | _, _ => .top



-- inductive AbsString where
--   | top | val : String → AbsString | bottom

inductive AbsVal where
  | num : Interval -> AbsVal
  | bool : AbsBool -> AbsVal
  | ref : Addr -> AbsVal
  | top : AbsVal
  | bottom : AbsVal
deriving Repr, DecidableEq, Inhabited

def AbsVal.join (v1 v2: AbsVal): AbsVal := match v1, v2 with
  | .bottom, v => v
  | v, .bottom => v
  | .top, _ => .top
  | _, .top => .top
  | .num i1, .num i2 => .num (Interval.join i1 i2)
  | .bool b1, .bool b2 => .bool (AbsBool.join b1 b2)
  | .ref a1, .ref a2 => if a1 == a2 then .ref a1 else .top
  | _, _ => top -- mismatchd types (error? )

-- Alias for backwards compatibility (join is now pure, no widening)
def AbsVal.pureJoin (v1 v2: AbsVal): AbsVal := AbsVal.join v1 v2

-- Equality check for abstract values
def AbsVal.eq_decidable (v1 v2 : AbsVal) : Bool := match v1, v2 with
  | .bottom, .bottom => true
  | .top, .top => true
  | .num i1, .num i2 => Interval.eq_decidable i1 i2
  | .bool b1, .bool b2 => b1 == b2
  | .ref a1, .ref a2 => a1 == a2
  | _, _ => false
