import Std
open Std

/-!
  Access Control Model
  Backend verification logic using Lean 4
-/

-- Define users of the system
inductive User where
  | alice
  | bob
  | eve
  deriving DecidableEq, Repr

-- Define protected resources
inductive Resource where
  | fileA
  | fileB
  deriving DecidableEq, Repr

-- Access policy definition
def canAccess (u : User) (r : Resource) : Prop :=
  match u, r with
  | User.alice, Resource.fileA => True
  | User.bob,   Resource.fileA => True
  | _, _ => False

-- Security property:
-- If a user can access a resource, they must be authorised
def accessSecure (u : User) (r : Resource) : Prop :=
  canAccess u r → (u = User.alice ∨ u = User.bob)

-- Proof that the access control policy is secure
theorem access_control_is_secure :
  ∀ u r, accessSecure u r := by
  intro u r
  unfold accessSecure
  intro h
  cases u <;> cases r <;> simp [canAccess] at h
  · exact Or.inl rfl
  · exact Or.inr rfl