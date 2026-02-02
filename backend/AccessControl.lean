import Std
open Std

/-!
  Access Control Model

  Backend verification logic using Lean 4

  This code file defines a simple access control policy and formally verifies a security property
  using the Lean 4 theorem prover.

  This model was implemented to demonstrate how formal methods can be used to mathematically prove 
  security properties and provide a guaranteed answer, instead of just relying on testing or simulation. 
  
-/

/-- 
Represents the users of the system
For demonstration reasons, the model includes:

- Two authorised users (Alice and Bob)
- One unauthorised user (Eve)
-/

inductive User where
  | alice
  | bob
  | eve
  deriving DecidableEq, Repr

/-- 
Defines the protected resources in the system
These resources are used within the access control policies
-/

inductive Resource where
  | fileA
  | fileB
  deriving DecidableEq, Repr

/--
The Access Control policy definition

This policy specifies which users are allowed to access which resources

In this model:
- Alice and Bob may access File A
- All other access attempts are denied
-/

def canAccess (u : User) (r : Resource) : Prop :=
  match u, r with
  | User.alice, Resource.fileA => True
  | User.bob,   Resource.fileA => True
  | _, _ => False

/-- 
Security property check for Access Control

If a user can access a resource, they must be authorised
This property displays the idea that unauthorised users (in this case, Eve) can never gain access
-/

def accessSecure (u : User) (r : Resource) : Prop :=
  canAccess u r → (u = User.alice ∨ u = User.bob)

/--
The Formal Proof that the access control policy is secure

This theorem proves that for all users and resources, the accessSecure property holds
This proof:
- Performs case analysis on users and resources
- Simplifies the access control policy
- Shows that only Alice and Bob can satisfy the property
-/

theorem access_control_is_secure :
  ∀ u r, accessSecure u r := by
  intro u r
  unfold accessSecure
  intro h
  cases u <;> cases r <;> simp [canAccess] at h
  · exact Or.inl rfl
  · exact Or.inr rfl