// SPDX-License-Identifier: MIT
//
//============================================================================
//     A Pedagogical, Literate Implementation of a Bit Commitment OR-Proof
// ----------------------------------------------------------------------------
//     This Scala3 source file is written in the spirit of *literate programming*:
//     the intent is not only to execute correctly, but also to *teach*.  Each
//     concept is introduced gradually, through explanatory commentary before
//     its code.  The final program implements a fully‑working demonstration of
//     a zero‑knowledge "bit commitment" proof—where a prover shows that a sealed
//     commitment corresponds to either bit 0 or bit 1, without revealing which.
//
//============================================================================
//
// TABLE OF CONTENTS
// -----------------
//   1. Intuition: Commitments and Zero‑Knowledge OR‑Proofs
//   2. Abstract Algebraic Foundations: The Generic Group Interface
//   3. Data Structures for Commitments and Proofs
//   4. The Bit Commitment Protocol (prove / verify)
//   5. Instantiating a Concrete Group (modular arithmetic over Z_p*)
//   6. Demonstration and Interpretation
//
//============================================================================

package zk

// Basic imports from the standard library we will use later
import java.security.MessageDigest
import scala.util.{Random, boundary}
import boundary.break


//============================================================================
// 1. INTUITION: COMMITMENTS AND ZERO‑KNOWLEDGE LOGIC
// ----------------------------------------------------------------------------
//
//   The goal: Make a cryptographic "envelope" that hides a bit b ∈ {0,1} while
//   allowing the prover to convince others that it truly encodes a well‑formed
//   bit—either 0 or 1—but without revealing which.
//
//   The commitment form resembles the well‑known *Pedersen commitment*:
//
//       C = rH + bG
//
//   where:
//      – G is a public group generator,
//      – H is another generator whose discrete log relative to g is unknown,
//      – r is random secret
//
//   If b = 0, the commitment becomes C = rH.
//   If b = 1, the commitment becomes C = rH + G.
//
//   Both look equally random to outsiders.
//
//   To prove correctness of C without disclosing b, we use an
//   *OR‑proof of knowledge*:
//
//      “I know an r such that C = rH    (b=0)
//       **or**
//       I know an r such that C - G = rH (b=1).”
//
//   The challenge: prove this disjunction non‑interactively in zero‑knowledge.
//   The solution: a *Σ‑protocol composition* with one simulated branch,
//   and the Fiat–Shamir heuristic to derive an overall challenge hash.
//
//============================================================================


//============================================================================
// 2. ABSTRACT ALGEBRAIC FOUNDATIONS
// ----------------------------------------------------------------------------
//   The protocol must work over any *abelian group*: there is no need to commit
//   to an implementation (elliptic curves, multiplicative integers mod p, etc.).
//   We therefore define a small functional trait that exposes *only* the group
//   operations we require.
//
//   This design clarifies what mathematics the protocol relies upon, and allows
//   us to instantiate the same logic in any group supporting these primitives.
//============================================================================
trait AbelianGroup[E]:

  // --- Core algebraic operations ------------------------------------------------
  def identity: E                      // Neutral element (1 for multiplication)
  def add(a: E, b: E): E               // Group operation: a + b
  def multByScalar(base: E, exponent: BigInt): E // Mult by integer
  def inverse(a: E): E                 // Inverse of a
  def generator: E                     // Public generator g
  def order: BigInt                    // Group order |G|

  // --- Cryptographic utilities --------------------------------------------------
  //
  // These represent the "glue" between protocol messages and randomness.
  def hashToGroupElement(input: String): E    // Deterministic generator derivation
  def randomScalar(): BigInt                  // Uniform scalar mod |G|
  def challenge(context: String, parts: Seq[Any]): BigInt // Fiat–Shamir hash

  // Optional pretty-print
  def debugToString(e: E): String = e.toString

//============================================================================
// 2.1. Syntax Extensions for Group Operations
// ----------------------------------------------------------------------------
//   These extensions allow more natural syntax for group operations. Since the
//   group is Abelian (commutative) we adopt the additive syntax.
//============================================================================
extension [E](a: E)(using G: AbelianGroup[E])
  /** Addition (group operation): `A + B` */
  def +(b: E): E = G.add(a, b)

  /** Multiply by scalar from the right: `A * n` */
  def *(n: BigInt): E = G.multByScalar(a, n)

  /** Inverse: `-A` */
  def unary_- :E = G.inverse(a)

  /** Subtraction: `A - B` */
  def -(b: E) : E = a + G.inverse(b)

  /** Pretty-print */
  def show: String = G.debugToString(a)

extension (scalar: BigInt | Int)
  /** Multiply by scalar from the left: `scalar * A` */
  def *[E](b: E)(using G: AbelianGroup[E]) = scalar match
    case n: Int => G.multByScalar(b,BigInt(n))
    case n: BigInt => G.multByScalar(b,n)

//============================================================================
// 3. REPRESENTING COMMITMENTS AND PROOFS
// ----------------------------------------------------------------------------
//   Before delving into the protocol implementation, we clarify *what data* each
//   actor produces and verifies.
//
//   When a prover produces a proof that a commitment is well‑formed, that proof
//   transcript needs to carry a few public values:
//
//     • "T" values: the first messages (commitments) from each branch (for bits 0, 1)
//     • "e" values: the split challenges corresponding to each branch
//     • "z" values: the responses to those challenges
//
//   We group them into a structure, `BitOrProof`.  A `BitCommitment` then pairs
//   the main commitment `C` with its associated proof transcript.
//============================================================================
case class BitOrProof[E](
    Tfor0: E, Tfor1: E,         // First message for branch 0, 1
    eFor0: BigInt, eFor1: BigInt, // Split challenges
    zFor0: BigInt, zFor1: BigInt  // Responses
)

case class BitCommitment[E](
    commitment: E,       // The actual sealed commitment C = rH + bG
    proof: BitOrProof[E] // The attached zero‑knowledge OR‑proof
)



//============================================================================
// 4. THE BIT COMMITMENT PROTOCOL
// ----------------------------------------------------------------------------
//   This section is the intellectual heart of the file.  It implements the logic
//   of constructing and checking a *non‑interactive zero‑knowledge OR‑proof*.
//
//   The essence:
//
//      - The prover picks a random r and forms a commitment C = rH + bG.
//      - They honestly prove knowledge for the true branch’s equation.
//      - They *simulate* the false branch (choose its challenge/response first).
//      - Using Fiat–Shamir, both branches are tied to a single global challenge.
//
//   Because one side is simulated and the other honest, yet both blend together
//   in the hash equation eTotal = e0 + e1, a verifier cannot tell which was real.
//============================================================================
class BitCommitProtocol[E](using group: AbelianGroup[E]):
  import group.*

  val G = generator

  // A secondary generator H.  It must have an unknown discrete log relative to g.
  // We derive it deterministically by hashing a label into the group.
  private val H = hashToGroupElement("second_generator")


  //--------------------------------------------------------------------------
  // PROVER LOGIC
  //--------------------------------------------------------------------------
  def prove(bit: Int): BitCommitment[E] =
    require(bit == 0 || bit == 1, "Bit must be 0 or 1")

    // --- Step 1: form basic commitment -------------------------------------
    val r = randomScalar()
    val commitment = (r*H) + (bit*G)

    // For clarity, define related representations of the two statements:
    val A = commitment        // for “C = rH” (bit 0)
    val B = commitment - G    // for “C - G = rH” (bit 1)

    // Depending on the true bit, we choose which branch to simulate.
    // ----------------------------------------------------------------
    // The prover genuinely *knows* the witness r for one of the two statements:
    //
    //    (true branch)   A = rH        → for bit = 0
    //    (false branch)  B = rH        → for bit = 1
    //
    // The prover will build a *real* Σ-protocol transcript for the true one,
    // and a *simulated* transcript for the other. The key is that both end up
    // consistent with a single global challenge hash, so the verifier cannot
    // tell which side was faked.

    if bit == 0 then

      //-----------------------------------------------------------------------
      // (A) Honest subproof for the true statement: “I know r such that A = g^r”
      //-----------------------------------------------------------------------
      //
      // As in a classic discrete log Σ-protocol:
      //   1. Choose a random nonce k₀.
      //   2. Send T₀ = k₀H as the first message.
      //
      // Later, when the challenge e₀ is known, respond with z₀ = k₀ + e₀·r.
      //-----------------------------------------------------------------------
      val k0 = randomScalar()
      val T0 = k0*H     // T₀ = k₀*H


      //-----------------------------------------------------------------------
      // (B) Simulated subproof for the *other* (false) branch.
      //-----------------------------------------------------------------------
      //
      // We have no witness r₁ for "B = r₁H" (since bit ≠ 1),
      // but we can *simulate* what a real transcript would look like.
      //
      // A valid transcript for that branch would satisfy:
      //
      //     z₁*H = T₁ + e₁*B
      //
      // for some challenge e₁ chosen by the verifier.  But since we are
      // generating the proof non‑interactively, **we** pick e₁ and z₁ first,
      // then algebraically define t₁ so that the above verification equation
      // will *automatically* hold.
      //
      // Rearranging the verification equation:
      //
      //     T₁ = z₁*H - e₁*B
      //
      // gives exactly the formula used below.
      //
      // This “forged” T₁ looks random to anyone who doesn’t know r₁, because
      // both e₁ and z₁ are uniformly random.  Yet it will *verify correctly*
      // once those values are plugged back in downstream.
      //-----------------------------------------------------------------------
      val e1 = randomScalar()  // Simulated challenge (as if issued by verifier)
      val z1 = randomScalar()  // Simulated response
      val T1 = (z1*H) - (e1*B) 
      // Ensures the formal identity z₁*H = T₁ + e₁*B will hold true later.


      //-----------------------------------------------------------------------
      // (C) Merging both branches via the Fiat–Shamir heuristic.
      //-----------------------------------------------------------------------
      //
      // At this point, we have *two half‑proofs*:
      //     • one real (A, T₀) awaiting its challenge e₀,
      //     • one simulated (B, T₁, e₁, z₁) already self‑consistent.
      //
      // How to tie them into one coherent, verifier‑checkable whole?
      //
      // We hash all public elements of the transcript — A, B, T₀, T₁ —
      // into a single deterministic scalar eTotal:
      //
      //            eTotal = HASH(A, B, T₀, T₁)
      //
      // Then we enforce that the individual branch challenges must partition
      // this total challenge:
      //
      //            eTotal = e₀ + e₁ (mod q)
      //
      // The prover thus computes:
      //
      //            e₀ = eTotal − e₁  (mod q)
      //
      // guaranteeing that when the verifier recomputes the same hash eTotal,
      // the sum consistency check will succeed.
      //
      // Why this works conceptually:
      //   • It makes the simulated branch “feel” like it came from the same
      //     random oracle as the real one — blending them together.
      //   • The verifier’s view is identical whether bit=0 or bit=1; only
      //     one branch was real, but the commitments and challenges fit
      //     together algebraically in the same way.
      //
      // Finally, for the honest branch we compute its matching response z₀:
      //
      //            z₀ = k₀ + e₀·r  (mod q)
      //
      //-----------------------------------------------------------------------
      val eTotal = challenge("bit-proof", Seq(A, B, T0, T1))
      val e0 = (eTotal - e1 + order) % order
      val z0 = (k0 + (e0 * r)) % order  // honest response

      // The transcript (T₀, T₁, e₀, e₁, z₀, z₁) now satisfies both verifier equations
      // and the challenge‑sum constraint, convincing yet zero‑knowledge.
      BitCommitment(commitment, BitOrProof(T0, T1, e0, e1, z0, z1))

    else
      // Symmetric case: bit = 1, so the B-branch is honest.
      val k1 = randomScalar()
      val T1 = k1*H

      // Simulate the false branch for bit=0:
      val e0 = randomScalar()
      val z0 = randomScalar()
      val T0 = (H*z0) - (A*e0)

      val eTotal = challenge("bit-proof", Seq(A, B, T0, T1))
      val e1 = (eTotal - e0 + order) % order
      val z1 = (k1 + (e1 * r)) % order

      BitCommitment(commitment, BitOrProof(T0, T1, e0, e1, z0, z1))



  //--------------------------------------------------------------------------
  // VERIFIER LOGIC
  //--------------------------------------------------------------------------
  //
  // The verifier repeats the structural relationships implied by the proof
  // transcript and checks that they hold consistently, *without* knowing which
  // branch is real.
  //
  //   Requirements:
  //     (1) Challenges add up: eTotal = e0 + e1  (from the hash)
  //     (2) Each branch equation holds:
  //           z0*H ?= T0 + e0*A
  //           z1*H ?= T1 + e1*B
  //--------------------------------------------------------------------------
  def verify(bitCommit: BitCommitment[E]): Boolean = boundary:
    val commitment = bitCommit.commitment
    val pf = bitCommit.proof
    val A = commitment
    val B = commitment - G

    val eTotal = challenge("bit-proof", Seq(A, B, pf.Tfor0, pf.Tfor1))

    // Check challenge consistency
    if ((pf.eFor0 + pf.eFor1) % order) != eTotal then break(false)

    // Check both branch equations
    val ok0 = (H * pf.zFor0) == (pf.Tfor0 + (A*pf.eFor0))
    val ok1 = (H * pf.zFor1) == (pf.Tfor1 + (B*pf.eFor1))

    // If both equations hold, the proof transcript is sound and
    // zero‑knowledge with respect to which bit was committed.
    ok0 && ok1



//============================================================================
// 5. CONCRETE INSTANTIATION: MULTIPLICATIVE GROUP MOD p
// ----------------------------------------------------------------------------
//   To make the protocol executable, we pick a concrete group implementation.
//   Here we use the multiplicative group (Z/pZ)* where p is the same large
//   prime as that used by Bitcoin’s secp256k1.  This example provides complete
//   functionality for experimentation.
//
//   The following object is purely functional — no mutation or side‑effects.
//   It implements the `AbelianGroup` interface required by the protocol above.
//============================================================================
opaque type ZModP = BigInt
given ModPGroup: AbelianGroup[ZModP]:
  val P: BigInt = BigInt("FFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEFFFFFC2F", 16)
  val g: BigInt = 3

  override val identity: ZModP = 1
  override val generator: ZModP = g
  override val order: BigInt = P - 1

  private def mod(x: BigInt): BigInt = ((x % P) + P) % P

  override def add(a: ZModP, b: ZModP): ZModP = mod(a * b)

  override def multByScalar(a: ZModP, exp: ZModP): ZModP =
    if exp >= 0 then a.modPow(exp, P)
    else a.modPow(-exp, P).modInverse(P)

  override def inverse(a: ZModP): ZModP = a.modInverse(P)

  private def hashBytes(s: String): Array[Byte] =
    val md = MessageDigest.getInstance("SHA-256")
    md.digest(s.getBytes("UTF-8"))

  // Map hash string deterministically to group element
  override def hashToGroupElement(input: String): ZModP =
    val h = BigInt(1, hashBytes(input)) % P
    if h == 0 then 1 else h

  // seed a random number generator so that tests are reproducible
  private val rnd = Random(seed = 42L)
  override def randomScalar(): BigInt =
    BigInt(order.bitLength, rnd) % order

  override def challenge(context: String, parts: Seq[Any]): BigInt =
    val msg = context + ":" + parts.map(_.toString).mkString(":")
    val digest = BigInt(1, hashBytes(msg))
    digest % order



//============================================================================
// 6. DEMONSTRATION AND INTERPRETATION
// ----------------------------------------------------------------------------
//   The short demo below exercises the entire protocol:
//     • It generates proofs for both bit values (0 and 1)
//     • Shows that verification accepts each
//     • Demonstrates that tampering with the transcript breaks validity
//
//   Conceptually, a successful run teaches:
//
//     - From the outside, both proofs look identical in structure.
//     - The zero‑knowledge property ensures no information about b leaks.
//     - If the commitment is malformed or altered, verification fails.
//
//   This is therefore a *complete pedagogical implementation* of a practical
//   cryptographic primitive, expressed in a purely functional, educational style.
//============================================================================
object Demo:
  def main(args: Array[String]): Unit =
    val group = ModPGroup
    val protocol = new BitCommitProtocol(using group)

    println("\n==== Bit Commitment OR‑Proof Demonstration ====\n")

    // Try both bit values
    for bit <- Seq(0, 1) do
      val proof = protocol.prove(bit)
      val valid = protocol.verify(proof)
      println(s"Bit=$bit → Commitment=${group.debugToString(proof.commitment)}")
      println(s"Verified=$valid\n")

    // Tamper with a valid proof to demonstrate detection
    val honest = protocol.prove(0)
    val tamperedCommitment = group.add(honest.commitment, honest.commitment)
    val tampered = honest.copy(commitment = tamperedCommitment)
    val invalid = protocol.verify(tampered)
    println(s"Tampered commitment → Verification: $invalid\n")