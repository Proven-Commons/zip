/-
  Proofs about the DEFLATE reader and writer in `Inflate.lean`.

  The headline result is `inflate_deflateStored`: inflating what
  the stored-block writer wrote gives the input back, for every
  input. The proof goes through the bit lemmas below: a stored
  block is a header byte, a length and its complement, and the raw
  bytes, and each read the decoder makes on that shape is computed
  exactly.

  A second headline, `inflate_deflateFixed`, is proved in the
  last section: inflating what the fixed Huffman writer wrote
  gives the input back, for every input. The dynamic table case
  still rests on the differential tests recorded in
  tests/TEST-RESULTS.md.
-/

import ZipPilot.Inflate

namespace ZipPilot

/-! ## Bit list lemmas -/

theorem valOfBits_append (l₁ l₂ : List Bool) :
    valOfBits (l₁ ++ l₂) = valOfBits l₁ + 2 ^ l₁.length * valOfBits l₂ := by
  induction l₁ with
  | nil => simp [valOfBits]
  | cons b l₁ ih =>
    have e1 : valOfBits (b :: (l₁ ++ l₂)) =
        (if b then 1 else 0) + 2 * valOfBits (l₁ ++ l₂) := rfl
    have e2 : valOfBits (b :: l₁) =
        (if b then 1 else 0) + 2 * valOfBits l₁ := rfl
    rw [List.cons_append, e1, e2, ih, List.length_cons,
      show (2 : Nat) ^ (l₁.length + 1) = 2 ^ l₁.length * 2 from
        Nat.pow_succ 2 l₁.length,
      Nat.mul_comm (2 ^ l₁.length) 2, Nat.mul_assoc, Nat.mul_add]
    omega

theorem valOfBits_lt (l : List Bool) : valOfBits l < 2 ^ l.length := by
  induction l with
  | nil => simp [valOfBits]
  | cons b bs ih =>
    have hbit : (if b then 1 else 0) ≤ 1 := by cases b <;> simp
    have e1 : valOfBits (b :: bs) =
        (if b then 1 else 0) + 2 * valOfBits bs := rfl
    rw [e1, List.length_cons,
      show (2 : Nat) ^ (bs.length + 1) = 2 ^ bs.length * 2 from
        Nat.pow_succ 2 bs.length]
    omega

theorem bitsOfNat_length (n v : Nat) : (bitsOfNat n v).length = n := by
  induction n generalizing v with
  | zero => rfl
  | succ n ih => rw [bitsOfNat, List.length_cons, ih]

theorem bitsOfNat_zero (n : Nat) : bitsOfNat n 0 = List.replicate n false := by
  induction n with
  | zero => rfl
  | succ n ih => rw [bitsOfNat, ih]; rfl

theorem valOfBits_bitsOfNat (n v : Nat) (h : v < 2 ^ n) :
    valOfBits (bitsOfNat n v) = v := by
  induction n generalizing v with
  | zero =>
    have : v = 0 := by omega
    subst this
    rfl
  | succ n ih =>
    have hbit : (if decide (v % 2 = 1) then (1 : Nat) else 0) = v % 2 := by
      rcases Nat.mod_two_eq_zero_or_one v with h0 | h0 <;> simp only [h0] <;> decide
    have hlt : v / 2 < 2 ^ n := by
      have hpow : (2 : Nat) ^ (n + 1) = 2 ^ n * 2 := Nat.pow_succ 2 n
      rw [hpow] at h
      omega
    have hv : valOfBits (bitsOfNat (n + 1) v) =
        (if decide (v % 2 = 1) then 1 else 0) +
          2 * valOfBits (bitsOfNat n (v / 2)) := rfl
    rw [hv, hbit, ih (v / 2) hlt]
    omega

theorem bitsOfNat_valOfBits (l : List Bool) (k m : Nat)
    (h : l.length + k = m) :
    bitsOfNat m (valOfBits l) = l ++ bitsOfNat k 0 := by
  induction l generalizing k m with
  | nil =>
    have h2 : k = m := by simpa using h
    subst h2
    simp [valOfBits]
  | cons b bs ih =>
    rcases m with _ | m'
    · rw [List.length_cons] at h; omega
    · have h' : bs.length + k = m' := by
        rw [List.length_cons] at h; omega
      have hv : valOfBits (b :: bs) =
          (if b then 1 else 0) + 2 * valOfBits bs := rfl
      have hmod : (valOfBits (b :: bs)) % 2 = (if b then 1 else 0) := by
        rw [hv]
        cases b
        · show (0 + 2 * valOfBits bs) % 2 = 0; omega
        · show (1 + 2 * valOfBits bs) % 2 = 1; omega
      have hdiv : (valOfBits (b :: bs)) / 2 = valOfBits bs := by
        rw [hv]
        cases b
        · show (0 + 2 * valOfBits bs) / 2 = valOfBits bs; omega
        · show (1 + 2 * valOfBits bs) / 2 = valOfBits bs; omega
      have hstep : bitsOfNat (m' + 1) (valOfBits (b :: bs)) =
          decide (valOfBits (b :: bs) % 2 = 1) ::
            bitsOfNat m' (valOfBits (b :: bs) / 2) := rfl
      rw [hstep, hmod, hdiv, ih k m' h', List.cons_append]
      cases b <;> rfl

theorem byteBits_val (b : UInt8) : valOfBits (byteBits b) = b.toNat :=
  valOfBits_bitsOfNat 8 b.toNat (by exact UInt8.toNat_lt b)

theorem bitsToByte_byteBits (b : UInt8) : bitsToByte (byteBits b) = b := by
  rw [bitsToByte, byteBits_val]
  exact UInt8.ofNat_toNat

theorem bytesToBits_cons (b : UInt8) (bs : List UInt8) :
    bytesToBits (b :: bs) = byteBits b ++ bytesToBits bs := rfl

theorem bytesToBits_append (a b : List UInt8) :
    bytesToBits (a ++ b) = bytesToBits a ++ bytesToBits b := by
  induction a with
  | nil => simp [bytesToBits]
  | cons x xs ih =>
    simp only [List.cons_append, bytesToBits_cons, ih, List.append_assoc]

theorem bytesToBits_length (bs : List UInt8) :
    (bytesToBits bs).length = 8 * bs.length := by
  induction bs with
  | nil => rfl
  | cons b bs ih =>
    rw [bytesToBits_cons, List.length_append, ih, List.length_cons]
    have : (byteBits b).length = 8 := bitsOfNat_length 8 b.toNat
    omega

/-! ## Reading bytes back -/

theorem readBytesAux_eq (data : List UInt8) (more : List Bool) :
    readBytesAux data.length (bytesToBits data ++ more) = (data, more) := by
  induction data generalizing more with
  | nil => rfl
  | cons b bs ih =>
    have h1 : bytesToBits (b :: bs) ++ more =
        byteBits b ++ (bytesToBits bs ++ more) := by
      rw [bytesToBits_cons, List.append_assoc]
    rw [List.length_cons, h1, readBytesAux]
    have htake : (byteBits b ++ (bytesToBits bs ++ more)).take 8 = byteBits b :=
      List.take_left' (bitsOfNat_length 8 b.toNat)
    have hdrop : (byteBits b ++ (bytesToBits bs ++ more)).drop 8 =
        bytesToBits bs ++ more :=
      List.drop_left' (bitsOfNat_length 8 b.toNat)
    rw [htake, hdrop, bitsToByte_byteBits, ih]

theorem readBytes_eq (data : List UInt8) (more : List Bool) (p : Nat) :
    readBytes data.length ⟨bytesToBits data ++ more,
        (bytesToBits data ++ more).length, p⟩ =
      some (data, ⟨more, more.length, p + 8 * data.length⟩) := by
  rw [readBytes]
  have hlen : ¬ (bytesToBits data ++ more).length < 8 * data.length := by
    rw [List.length_append, bytesToBits_length]
    omega
  rw [if_neg hlen, readBytesAux_eq,
    show (bytesToBits data ++ more).length - 8 * data.length = more.length by
      rw [List.length_append, bytesToBits_length]; omega]

/-! ## Folding bytes into the output -/

theorem toList_foldl_push (bs : List UInt8) (a : Array UInt8) :
    (bs.foldl Array.push a).toList = a.toList ++ bs := by
  induction bs generalizing a with
  | nil => simp
  | cons b bs ih =>
    rw [List.foldl_cons, ih, Array.toList_push, List.append_assoc]
    simp

theorem size_foldl_push (bs : List UInt8) (a : Array UInt8) :
    (bs.foldl Array.push a).size = a.size + bs.length := by
  induction bs generalizing a with
  | nil => simp
  | cons b bs ih =>
    rw [List.foldl_cons, ih, Array.size_push, List.length_cons]
    omega

/-! ## The reads a stored block makes -/

theorem readBits_one (h : UInt8) (Y : List Bool) (p : Nat) :
    readBits 1 ⟨byteBits h ++ Y, (byteBits h ++ Y).length, p⟩ =
      some (h.toNat % 2, ⟨bitsOfNat 7 (h.toNat / 2) ++ Y,
        (bitsOfNat 7 (h.toNat / 2) ++ Y).length, p + 1⟩) := by
  rw [readBits]
  have hlen : ¬ (byteBits h ++ Y).length < 1 := by
    rw [List.length_append]
    have h8 : (byteBits h).length = 8 := bitsOfNat_length 8 h.toNat
    omega
  rw [if_neg hlen,
    show (byteBits h ++ Y).length - 1 =
        (bitsOfNat 7 (h.toNat / 2) ++ Y).length by
      have h8 : (byteBits h).length = 8 := bitsOfNat_length 8 h.toNat
      rw [List.length_append, List.length_append, h8, bitsOfNat_length];
      omega]
  have hval : valOfBits [decide (h.toNat % 2 = 1)] = h.toNat % 2 := by
    rcases Nat.mod_two_eq_zero_or_one h.toNat with h0 | h0 <;>
      simp only [h0] <;> decide
  have htake : (byteBits h ++ Y).take 1 = [decide (h.toNat % 2 = 1)] := rfl
  have hdrop : (byteBits h ++ Y).drop 1 = bitsOfNat 7 (h.toNat / 2) ++ Y := rfl
  rw [htake, hdrop, hval]

theorem readBits_twoZeros (Y : List Bool) (p : Nat) :
    readBits 2 ⟨List.replicate 7 false ++ Y,
        (List.replicate 7 false ++ Y).length, p⟩ =
      some (0, ⟨List.replicate 5 false ++ Y,
        (List.replicate 5 false ++ Y).length, p + 2⟩) := by
  rw [readBits]
  have hlen : ¬ (List.replicate 7 false ++ Y).length < 2 := by
    rw [List.length_append, List.length_replicate]
    omega
  rw [if_neg hlen,
    show (List.replicate 7 false ++ Y).length - 2 =
        (List.replicate 5 false ++ Y).length by
      rw [List.length_append, List.length_append, List.length_replicate,
        List.length_replicate]; omega]
  have htake : (List.replicate 7 false ++ Y).take 2 = [false, false] := rfl
  have hdrop : (List.replicate 7 false ++ Y).drop 2 =
      List.replicate 5 false ++ Y := rfl
  have hval : valOfBits [false, false] = 0 := rfl
  rw [htake, hdrop, hval]

theorem alignByte_step (Y : List Bool) (p : Nat) (hp : p % 8 = 3) :
    alignByte ⟨List.replicate 5 false ++ Y,
        (List.replicate 5 false ++ Y).length, p⟩ =
      ⟨Y, Y.length, p + 5⟩ := by
  show (⟨(List.replicate 5 false ++ Y).drop ((8 - p % 8) % 8),
      (List.replicate 5 false ++ Y).length - (8 - p % 8) % 8,
      p + (8 - p % 8) % 8⟩ : BR) = ⟨Y, Y.length, p + 5⟩
  have hd : (8 - p % 8) % 8 = 5 := by rw [hp]
  rw [hd, List.drop_left' (show (List.replicate 5 false).length = 5 from
    List.length_replicate),
    show (List.replicate 5 false ++ Y).length - 5 = Y.length by
      rw [List.length_append, List.length_replicate]; omega]

theorem readBits_u16 (a b : UInt8) (Y : List Bool) (p : Nat) :
    readBits 16 ⟨byteBits a ++ (byteBits b ++ Y),
        (byteBits a ++ (byteBits b ++ Y)).length, p⟩ =
      some (a.toNat + 256 * b.toNat, ⟨Y, Y.length, p + 16⟩) := by
  rw [readBits]
  have hlen : ¬ (byteBits a ++ (byteBits b ++ Y)).length < 16 := by
    rw [List.length_append, List.length_append]
    have h1 : (byteBits a).length = 8 := bitsOfNat_length 8 a.toNat
    have h2 : (byteBits b).length = 8 := bitsOfNat_length 8 b.toNat
    omega
  rw [if_neg hlen,
    show (byteBits a ++ (byteBits b ++ Y)).length - 16 = Y.length by
      have h1 : (byteBits a).length = 8 := bitsOfNat_length 8 a.toNat
      have h2 : (byteBits b).length = 8 := bitsOfNat_length 8 b.toNat
      rw [List.length_append, List.length_append, h1, h2]; omega]
  have hla : (byteBits a).length = 8 := bitsOfNat_length 8 a.toNat
  have hlb : (byteBits b).length = 8 := bitsOfNat_length 8 b.toNat
  have htake : (byteBits a ++ (byteBits b ++ Y)).take 16 =
      byteBits a ++ byteBits b := by
    rw [List.take_append,
      List.take_of_length_le (show (byteBits a).length ≤ 16 by omega),
      show 16 - (byteBits a).length = 8 by rw [hla], List.take_left' hlb]
  have hdrop : (byteBits a ++ (byteBits b ++ Y)).drop 16 = Y := by
    rw [List.drop_append,
      List.drop_of_length_le (show (byteBits a).length ≤ 16 by omega),
      show 16 - (byteBits a).length = 8 by rw [hla], List.drop_left' hlb,
      List.nil_append]
  rw [htake, hdrop]
  simp only [valOfBits_append, byteBits_val, hla]

/-! ## The stored block round trip

The writer's stored blocks are read back exactly. The chain of
lemmas: one stored block steps `blocks` once (`storedStep`), a
chain of stored blocks is read whole (`blocks_storedChain`), the
chunking covers the input (`chunksOf_spec`), and so inflating the
stored writing returns the input (`inflate_deflateStored`). -/

/-- One stored block, read by `blocks`: the header bit and type are
    read, the length fields agree by construction, the bytes are
    copied, and the reader lands on the next byte boundary at
    `p + 8 * (chunk.length + 5)`. The block is final exactly when
    `f` says so. -/
theorem storedStep (f : Bool) (chunk suffix : List UInt8) (p : Nat)
    (hp : p % 8 = 0) (hmax : chunk.length ≤ 65535)
    (out : Array UInt8) (cap fuel : Nat)
    (hcap : out.size + chunk.length ≤ cap) :
    blocks (fuel + 1) ⟨bytesToBits (storedBlockBytes f chunk ++ suffix),
        (bytesToBits (storedBlockBytes f chunk ++ suffix)).length, p⟩
        out cap =
      if f then some (chunk.foldl Array.push out)
      else blocks fuel ⟨bytesToBits suffix, (bytesToBits suffix).length,
          p + 8 * (chunk.length + 5)⟩
        (chunk.foldl Array.push out) cap := by
  have hblock : storedBlockBytes f chunk =
      ((if f then 1 else 0).toUInt8 :: (chunk.length % 256).toUInt8 ::
       (chunk.length / 256).toUInt8 :: ((65535 - chunk.length) % 256).toUInt8 ::
       ((65535 - chunk.length) / 256).toUInt8 :: chunk) := rfl
  have hbits : bytesToBits (storedBlockBytes f chunk ++ suffix) =
      byteBits (if f then 1 else 0).toUInt8 ++
      (byteBits (chunk.length % 256).toUInt8 ++
      (byteBits (chunk.length / 256).toUInt8 ++
      (byteBits ((65535 - chunk.length) % 256).toUInt8 ++
      (byteBits ((65535 - chunk.length) / 256).toUInt8 ++
      (bytesToBits chunk ++ bytesToBits suffix))))) := by
    rw [bytesToBits_append, hblock]
    simp only [bytesToBits_cons, List.append_assoc]
  have hval : ((if f then 1 else 0).toUInt8).toNat = if f then 1 else 0 := by
    cases f <;> rfl
  have hd2 : ((if f then 1 else 0).toUInt8).toNat / 2 = 0 := by
    rw [hval]; cases f <;> rfl
  have hbyte : ∀ x : Nat, x ≤ 65535 →
      ((x % 256).toUInt8).toNat = x % 256 ∧
      ((x / 256).toUInt8).toNat = x / 256 := by
    intro x hx
    constructor
    · have h1 : ((x % 256).toUInt8).toNat = (x % 256) % 256 := rfl
      rw [h1, Nat.mod_eq_of_lt (Nat.mod_lt x (by decide))]
    · have h1 : ((x / 256).toUInt8).toNat = (x / 256) % 256 := rfl
      rw [h1, Nat.mod_eq_of_lt (by omega : x / 256 < 256)]
  have hlen_val : ((chunk.length % 256).toUInt8).toNat +
        256 * ((chunk.length / 256).toUInt8).toNat = chunk.length := by
    rw [(hbyte chunk.length hmax).1, (hbyte chunk.length hmax).2]
    omega
  have hnlen_val : (((65535 - chunk.length) % 256).toUInt8).toNat +
        256 * (((65535 - chunk.length) / 256).toUInt8).toNat =
        65535 - chunk.length := by
    rw [(hbyte (65535 - chunk.length) (by omega)).1,
      (hbyte (65535 - chunk.length) (by omega)).2]
    omega
  rw [hbits, blocks]
  rw [readBits_one, hd2, bitsOfNat_zero]
  simp only [Option.bind_some]
  rw [readBits_twoZeros]
  simp only [Option.bind_some]
  rw [if_true]
  rw [alignByte_step _ _ (by omega : (p + 1 + 2) % 8 = 3)]
  rw [readBits_u16]
  simp only [Option.bind_some]
  rw [readBits_u16]
  simp only [Option.bind_some]
  rw [hlen_val, hnlen_val]
  rw [if_neg (fun (h : chunk.length + (65535 - chunk.length) ≠ 65535) =>
    h (by omega))]
  rw [readBytes_eq]
  simp only [Option.bind_some]
  rw [show p + 1 + 2 + 5 + 16 + 16 + 8 * chunk.length =
      p + 8 * (chunk.length + 5) by omega]
  rw [size_foldl_push]
  rw [if_neg (by omega : ¬ cap < out.size + chunk.length)]
  rw [hval]
  cases f with
  | true => rfl
  | false =>
    rw [if_neg (show ¬ ((if false = true then (1 : Nat) else 0) % 2 = 1)
        by decide),
      if_neg (show ¬ (false = true) by decide)]

/-- Summing chunk lengths with an accumulator: the accumulator
    just adds on. -/
theorem foldl_add_lengths (l : List (List UInt8)) (a : Nat) :
    l.foldl (fun n c => n + c.length) a =
      a + l.foldl (fun n c => n + c.length) 0 := by
  induction l generalizing a with
  | nil => simp
  | cons c cs ih =>
    show cs.foldl (fun n c => n + c.length) (a + c.length) =
      a + cs.foldl (fun n c => n + c.length) (0 + c.length)
    rw [ih (a + c.length), ih (0 + c.length)]
    omega

/-- A stored chain is at least as long, in bytes, as the chunk
    count: every block carries five header bytes. This is what
    bounds the fuel the reader needs. -/
theorem storedChainBytes_length_ge (chunks : List (List UInt8)) :
    chunks.length ≤ (storedChainBytes chunks).length := by
  induction chunks with
  | nil => exact Nat.zero_le _
  | cons c cs ih =>
    cases cs with
    | nil =>
      have h : (storedBlockBytes true c).length = c.length + 5 := rfl
      rw [show storedChainBytes [c] = storedBlockBytes true c from rfl, h]
      simp
    | cons c' cs' =>
      have h : (storedBlockBytes false c).length = c.length + 5 := rfl
      rw [show storedChainBytes (c :: c' :: cs') =
          storedBlockBytes false c ++ storedChainBytes (c' :: cs') from rfl,
        List.length_append, h,
        show (c :: c' :: cs').length = (c' :: cs').length + 1 from rfl]
      omega

/-- A whole chain of stored blocks is read back: with enough fuel
    and room under the cap, `blocks` turns the chain into the
    flattened chunks appended to the output so far. -/
theorem blocks_storedChain (chunks : List (List UInt8))
    (suffix : List UInt8) (p : Nat) (out : Array UInt8) (cap : Nat)
    (fuel : Nat) (hp : p % 8 = 0)
    (hmax : ∀ c ∈ chunks, c.length ≤ 65535)
    (hcap : out.size + chunks.foldl (fun n c => n + c.length) 0 ≤ cap)
    (hfuel : chunks.length + 1 ≤ fuel) :
    blocks fuel ⟨bytesToBits (storedChainBytes chunks ++ suffix),
        (bytesToBits (storedChainBytes chunks ++ suffix)).length, p⟩
        out cap =
      some (chunks.flatten.foldl Array.push out) := by
  induction chunks generalizing out fuel p with
  | nil =>
    obtain ⟨fuel', rfl⟩ : ∃ k, fuel = k + 1 := ⟨fuel - 1, by omega⟩
    show blocks (fuel' + 1)
      ⟨bytesToBits (storedBlockBytes true [] ++ suffix),
        (bytesToBits (storedBlockBytes true [] ++ suffix)).length, p⟩
        out cap =
      some ((List.flatten []).foldl Array.push out)
    rw [storedStep true [] suffix p hp (by simp) out cap fuel'
      (by simpa using hcap)]
    rfl
  | cons c cs ih =>
    obtain ⟨fuel', rfl⟩ : ∃ k, fuel = k + 1 := ⟨fuel - 1, by omega⟩
    cases cs with
    | nil =>
      show blocks (fuel' + 1)
        ⟨bytesToBits (storedBlockBytes true c ++ suffix),
          (bytesToBits (storedBlockBytes true c ++ suffix)).length, p⟩
          out cap =
        some ((List.flatten [c]).foldl Array.push out)
      rw [storedStep true c suffix p hp (hmax c (by simp)) out cap fuel'
        (by simpa using hcap)]
      simp [List.flatten]
    | cons c' cs' =>
      show blocks (fuel' + 1)
          ⟨bytesToBits (storedBlockBytes false c ++
            storedChainBytes (c' :: cs') ++ suffix),
            (bytesToBits (storedBlockBytes false c ++
              storedChainBytes (c' :: cs') ++ suffix)).length, p⟩ out cap =
        some ((List.flatten (c :: c' :: cs')).foldl Array.push out)
      rw [show storedBlockBytes false c ++ storedChainBytes (c' :: cs') ++
          suffix =
        storedBlockBytes false c ++
          (storedChainBytes (c' :: cs') ++ suffix) from List.append_assoc _ _ _]
      have htot : (c :: c' :: cs').foldl (fun n c => n + c.length) 0 =
          c.length + (c' :: cs').foldl (fun n c => n + c.length) 0 := by
        show (c' :: cs').foldl (fun n c => n + c.length) (0 + c.length) = _
        rw [foldl_add_lengths]
        omega
      rw [storedStep false c (storedChainBytes (c' :: cs') ++ suffix) p hp
        (hmax c (by simp)) out cap fuel' (by omega)]
      rw [ih (p + 8 * (c.length + 5)) (c.foldl Array.push out) fuel'
        (by omega)
        (fun x hx => hmax x (List.mem_cons_of_mem c hx))
        (by rw [size_foldl_push]; omega)
        (by simp only [List.length_cons] at hfuel ⊢; omega)]
      rw [if_neg (show ¬ (false = true) by decide),
        show (c :: c' :: cs').flatten = c ++ (c' :: cs').flatten from rfl,
        List.foldl_append]

/-- The chunking covers its input: the chunks flatten back to the
    data, their lengths add up to the data length, and no chunk
    passes the stored block limit. -/
theorem chunksOf_spec : ∀ (fuel : Nat) (data : List UInt8),
    data.length ≤ fuel →
      (chunksOf 65535 fuel data).flatten = data ∧
      (chunksOf 65535 fuel data).foldl (fun n c => n + c.length) 0 =
        data.length ∧
      ∀ c ∈ chunksOf 65535 fuel data, c.length ≤ 65535 := by
  intro fuel
  induction fuel with
  | zero =>
    intro data hlen
    have hnil : data = [] := by
      cases data with
      | nil => rfl
      | cons b bs =>
        simp only [List.length_cons] at hlen
        omega
    subst hnil
    exact ⟨rfl, rfl, fun c hc => by
      rw [show chunksOf 65535 0 [] = [] from rfl] at hc
      exact (List.not_mem_nil hc).elim⟩
  | succ fuel' ih =>
    intro data hlen
    cases data with
    | nil =>
      exact ⟨rfl, rfl, fun c hc => by
        rw [show chunksOf 65535 (fuel' + 1) [] = [] from rfl] at hc
        exact (List.not_mem_nil hc).elim⟩
    | cons b bs =>
      have hspec := ih ((b :: bs).drop 65535) (by
        rw [List.length_drop]; omega)
      have hshow : chunksOf 65535 (fuel' + 1) (b :: bs) =
          (b :: bs).take 65535 ::
            chunksOf 65535 fuel' ((b :: bs).drop 65535) := rfl
      rw [hshow]
      refine ⟨?_, ?_, ?_⟩
      · show (b :: bs).take 65535 ++
            (chunksOf 65535 fuel' ((b :: bs).drop 65535)).flatten = b :: bs
        rw [hspec.1, List.take_append_drop]
      · show (chunksOf 65535 fuel' ((b :: bs).drop 65535)).foldl
            (fun n c => n + c.length) (0 + ((b :: bs).take 65535).length) =
          (b :: bs).length
        rw [foldl_add_lengths, hspec.2.1, List.length_take, List.length_drop]
        omega
      · intro c hc
        cases hc with
        | head =>
          have h := List.length_take (i := 65535) (l := b :: bs)
          omega
        | tail _ hmem => exact hspec.2.2 c hmem

/-- Folding pushes onto an array lists exactly the pushed bytes. -/
theorem foldl_push_toList (l : List UInt8) (init : Array UInt8) :
    (l.foldl Array.push init).toList = init.toList ++ l := by
  induction l generalizing init with
  | nil => simp
  | cons b bs ih =>
    show (bs.foldl Array.push (init.push b)).toList = init.toList ++ b :: bs
    rw [ih, Array.toList_push, List.append_assoc]
    rfl

/-- The headline of this slice: inflating the writer's stored
    output returns the input, whenever the cap allows the input. -/
theorem inflate_deflateStored (data : List UInt8) (cap : Nat)
    (hcap : data.length ≤ cap) :
    inflate (deflateStored data) cap = some data := by
  have hspec := chunksOf_spec data.length data (Nat.le_refl _)
  have hmain : ∀ fuel : Nat,
      (chunksOf 65535 data.length data).length + 1 ≤ fuel →
      (blocks fuel ⟨bytesToBits (deflateStored data),
          (bytesToBits (deflateStored data)).length, 0⟩ #[] cap).map
          Array.toList = some data := by
    intro fuel hfuel
    have h1 : deflateStored data =
        storedChainBytes (chunksOf 65535 data.length data) ++ [] := by
      unfold deflateStored
      rw [List.append_nil]
    rw [h1, blocks_storedChain (chunksOf 65535 data.length data) [] 0 #[] cap
      fuel (by decide) hspec.2.2
      (by have h0 : (#[] : Array UInt8).size = 0 := rfl
          have h2 := hspec.2.1
          omega) hfuel,
      Option.map_some, hspec.1, foldl_push_toList]
    rfl
  rw [inflate]
  exact hmain _ (by
    unfold deflateStored
    rw [bytesToBits_length]
    have hge := storedChainBytes_length_ge (chunksOf 65535 data.length data)
    omega)

set_option maxRecDepth 1000000

/-! ## The fixed Huffman round trip

The headline here is `inflate_deflateFixed`: inflating what the
fixed Huffman writer wrote gives the input back, for every input,
whenever the cap allows it.

Why this was not proved before: the decoder walks the table built
by `buildHuff`, and a proof has to compute with that table. Most of
its fields are plain list folds and compute fine. The symbol list
was built with `List.mergeSort`, which the Lean kernel cannot
unfold at all (in this Lean version it is well founded recursion
under an irreducible definition), so no proof could ever evaluate
the table's symbol order. The builder now groups the symbols by
code length instead, which gives the same list by plain structural
recursion. The two builders were checked to agree on the fixed
tables and on thousands of generated length lists, and the whole
differential suite still passes. With that change the table is a
concrete value a proof can compute with: `fixedLitTable_eq` writes
it out in full and checks it by `decide`.

The inversion itself comes from `fixedLit_decode_closed_all`,
which checks, by one `decide` over the 257 symbols the writer can
emit (the 256 byte values and the end of block symbol), that
decoding a symbol's code from an empty tail returns the symbol and
consumes exactly its code. `huffDecode_go_append` is the general
step that carries a decode proved on a bare code into the middle
of a stream: if the walk stops exactly at the end of a bit list,
the same walk with more bits after it stops at the same symbol and
leaves the extra bits unread. The rest is plumbing of the same
shape as the stored round trip: symbol by symbol through
`decodeSymbols`, one step of `blocks`, and the packing of bits
back into bytes. -/

private instance : DecidableEq BR := fun a b =>
  decidable_of_iff (a.rest = b.rest ∧ a.rem = b.rem ∧ a.pos = b.pos) (by
    constructor
    · rintro ⟨h1, h2, h3⟩
      cases a; cases b; simp_all
    · intro h; rw [h]; exact ⟨rfl, rfl, rfl⟩)

private instance : DecidableEq Huff := fun a b =>
  decidable_of_iff (a.maxLen = b.maxLen ∧ a.counts = b.counts ∧
      a.firstCode = b.firstCode ∧ a.firstIdx = b.firstIdx ∧ a.syms = b.syms) (by
    constructor
    · rintro ⟨h1, h2, h3, h4, h5⟩
      cases a; cases b; simp_all
    · intro h; rw [h]; exact ⟨rfl, rfl, rfl, rfl, rfl⟩)

def fixedLitTableData : Huff :=
  ⟨9, #[0, 0, 0, 0, 0, 0, 0, 24, 152, 112], #[0, 0, 0, 0, 0, 0, 0, 0, 48, 400],
   #[0, 0, 0, 0, 0, 0, 0, 0, 24, 176], #[256, 257, 258, 259, 260, 261, 262, 263, 264, 265, 266, 267, 268, 269, 270, 271, 272, 273, 274, 275, 276, 277, 278, 279, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 80, 81, 82, 83, 84, 85, 86, 87, 88, 89, 90, 91, 92, 93, 94, 95, 96, 97, 98, 99, 100, 101, 102, 103, 104, 105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 280, 281, 282, 283, 284, 285, 286, 287, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236, 237, 238, 239, 240, 241, 242, 243, 244, 245, 246, 247, 248, 249, 250, 251, 252, 253, 254, 255]⟩

theorem fixedLitTable_eq : fixedLitTable = fixedLitTableData := by decide

def fixedCodeBits (s : Nat) : List Bool :=
  codeBits (canonCode fixedLitLengths s).1 (canonCode fixedLitLengths s).2

theorem fixedCodeBits_length (s : Nat) :
    (fixedCodeBits s).length = (canonCode fixedLitLengths s).2 := by
  rw [fixedCodeBits, codeBits, List.length_reverse]
  exact bitsOfNat_length _ _

theorem fixedLit_decode_closed_all :
    (List.range 257).all (fun s =>
      decide (huffDecode fixedLitTableData
          ⟨fixedCodeBits s, (fixedCodeBits s).length, 0⟩ =
        some (s, ⟨[], 0, (canonCode fixedLitLengths s).2⟩))) = true := by
  decide

theorem fixedLit_decode_closed (s : Nat) (hs : s < 257) :
    huffDecode fixedLitTableData
        ⟨fixedCodeBits s, (fixedCodeBits s).length, 0⟩ =
      some (s, ⟨[], 0, (canonCode fixedLitLengths s).2⟩) := by
  have h := List.all_eq_true.mp fixedLit_decode_closed_all s (List.mem_range.mpr hs)
  exact of_decide_eq_true h

theorem huffDecode_unfold (h : Huff) (r : BR) :
    huffDecode h r = huffDecode.go h h.maxLen 0 0 r := rfl

theorem go_zero (h : Huff) (code len : Nat) (r : BR) :
    huffDecode.go h 0 code len r = none := rfl

theorem go_nil (h : Huff) (fuel code len p : Nat) :
    huffDecode.go h (fuel + 1) code len ⟨[], 0, p⟩ = none := rfl

theorem go_step (h : Huff) (fuel code len : Nat) (b : Bool)
    (rest : List Bool) (p : Nat) :
    huffDecode.go h (fuel + 1) code len ⟨b :: rest, (b :: rest).length, p⟩ =
      if (h.firstCode[len + 1]?).getD 0 ≤ code * 2 + (if b then 1 else 0) &&
          code * 2 + (if b then 1 else 0) - (h.firstCode[len + 1]?).getD 0 <
            (h.counts[len + 1]?).getD 0 then
        some ((h.syms[(h.firstIdx[len + 1]?).getD 0 +
            (code * 2 + (if b then 1 else 0) - (h.firstCode[len + 1]?).getD 0)]?).getD 0,
          ⟨rest, rest.length, p + 1⟩)
      else huffDecode.go h fuel (code * 2 + (if b then 1 else 0)) (len + 1)
        ⟨rest, rest.length, p + 1⟩ := rfl

theorem huffDecode_go_append (h : Huff) :
    ∀ (fuel code len : Nat) (cb rest : List Bool) (p₀ p : Nat) (s : Nat),
      huffDecode.go h fuel code len ⟨cb, cb.length, p₀⟩ =
          some (s, ⟨[], 0, p₀ + cb.length⟩) →
      huffDecode.go h fuel code len ⟨cb ++ rest, (cb ++ rest).length, p⟩ =
        some (s, ⟨rest, rest.length, p + cb.length⟩) := by
  intro fuel
  induction fuel with
  | zero =>
    intro code len cb rest p₀ p s hstop
    rw [go_zero] at hstop
    cases hstop
  | succ fuel ih =>
    intro code len cb rest p₀ p s hstop
    cases cb with
    | nil =>
      simp only [List.length_nil, List.nil_append] at hstop
      rw [go_nil] at hstop
      cases hstop
    | cons b cb' =>
      have hp₀ : p₀ + (cb'.length + 1) = (p₀ + 1) + cb'.length := by omega
      have hp : p + (cb'.length + 1) = (p + 1) + cb'.length := by omega
      show huffDecode.go h (fuel + 1) code len
          ⟨b :: (cb' ++ rest), (b :: (cb' ++ rest)).length, p⟩ =
        some (s, ⟨rest, rest.length, p + (b :: cb').length⟩)
      rw [go_step] at hstop
      rw [go_step]
      by_cases hc : (decide ((h.firstCode[len + 1]?).getD 0 ≤
              code * 2 + (if b then 1 else 0)) &&
            decide (code * 2 + (if b then 1 else 0) -
              (h.firstCode[len + 1]?).getD 0 <
                (h.counts[len + 1]?).getD 0)) = true
      · rw [if_pos hc] at hstop
        rw [Option.some.injEq, Prod.mk.injEq, BR.mk.injEq] at hstop
        obtain ⟨hsv, hcb', _, hp1⟩ := hstop
        rw [if_pos hc, hsv, hcb']
        simp [hp1]
      · rw [if_neg hc] at hstop
        rw [if_neg hc, List.length_cons, hp] 
        rw [List.length_cons, hp₀] at hstop
        exact ih _ _ _ _ _ _ _ hstop

theorem huffDecode_fixedLit (s : Nat) (hs : s < 257) (rest : List Bool)
    (p : Nat) :
    huffDecode fixedLitTable ⟨fixedCodeBits s ++ rest,
        (fixedCodeBits s ++ rest).length, p⟩ =
      some (s, ⟨rest, rest.length, p + (canonCode fixedLitLengths s).2⟩) := by
  have hclosed := fixedLit_decode_closed s hs
  rw [huffDecode_unfold] at hclosed
  rw [← fixedCodeBits_length s] at hclosed
  have hclosed2 : huffDecode.go fixedLitTableData fixedLitTableData.maxLen
        0 0 ⟨fixedCodeBits s, (fixedCodeBits s).length, 0⟩ =
      some (s, ⟨[], 0, 0 + (fixedCodeBits s).length⟩) := by
    rw [Nat.zero_add]
    exact hclosed
  have h := huffDecode_go_append fixedLitTableData _ 0 0 _ rest 0 p s hclosed2
  rw [fixedLitTable_eq, huffDecode_unfold, ← fixedCodeBits_length s]
  exact h

theorem fixedLitLengths_getD (s : Nat) (hs : s < 288) :
    fixedLitLengths.getD s 0 =
      if s < 144 then 8 else if s < 256 then 9 else if s < 280 then 7 else 8 := by
  have h1 : fixedLitLengths.getD s 0 =
      (fixedLitLengths[s]?).getD 0 := by
    rw [List.getD_eq_getElem?_getD]
  rw [h1]
  have h2 : fixedLitLengths[s]? =
      some (if s < 144 then 8 else if s < 256 then 9 else if s < 280 then 7 else 8) := by
    show ((List.range 288).map (fun s =>
      if s < 144 then 8 else if s < 256 then 9 else if s < 280 then 7 else 8))[s]? = _
    rw [List.getElem?_map, List.getElem?_range]
    simp
    exact hs
  rw [h2]
  rfl

theorem canonCode_fixed_len_ge (s : Nat) (hs : s < 288) :
    7 ≤ (canonCode fixedLitLengths s).2 := by
  have h : (canonCode fixedLitLengths s).2 = fixedLitLengths.getD s 0 := rfl
  rw [h, fixedLitLengths_getD s hs]
  split
  · omega
  · split
    · omega
    · split <;> omega

theorem flatMap_fixedCodeBits_length (data : List UInt8) :
    data.length ≤ (data.flatMap (fun b => fixedCodeBits b.toNat)).length := by
  induction data with
  | nil => simp
  | cons b bs ih =>
    show (b :: bs).length ≤
      ((fixedCodeBits b.toNat) ++
        (bs.flatMap (fun b => fixedCodeBits b.toNat))).length
    rw [List.length_cons, List.length_append, fixedCodeBits_length]
    have h7 := canonCode_fixed_len_ge b.toNat (by
      have h := UInt8.toNat_lt b; omega)
    omega

theorem decodeSymbols_fixedLit (data : List UInt8) (fuel : Nat)
    (out : Array UInt8) (cap : Nat) (rest : List Bool) (p : Nat)
    (hfuel : data.length < fuel) (hcap : out.size + data.length ≤ cap) :
    decodeSymbols fuel fixedLitTable fixedDistTable
        ⟨(data.flatMap (fun b => fixedCodeBits b.toNat)) ++
          (fixedCodeBits 256 ++ rest),
          ((data.flatMap (fun b => fixedCodeBits b.toNat)) ++
            (fixedCodeBits 256 ++ rest)).length, p⟩ out cap =
      some (data.foldl Array.push out,
        ⟨rest, rest.length,
          p + ((data.flatMap (fun b => fixedCodeBits b.toNat)).length +
            (fixedCodeBits 256).length)⟩) := by
  induction data generalizing fuel out p with
  | nil =>
    obtain ⟨fuel', rfl⟩ : ∃ k, fuel = k + 1 := ⟨fuel - 1, by omega⟩
    show decodeSymbols (fuel' + 1) fixedLitTable fixedDistTable
          ⟨fixedCodeBits 256 ++ rest, (fixedCodeBits 256 ++ rest).length,
            p⟩ out cap =
        some (out, ⟨rest, rest.length,
          p + (canonCode fixedLitLengths 256).2⟩)
    rw [decodeSymbols, huffDecode_fixedLit 256 (by omega) rest p]
    simp only [Option.bind_some]
    rw [if_neg (show ¬ (256 < 256) by omega), if_true]
  | cons b bs ih =>
    obtain ⟨fuel', rfl⟩ : ∃ k, fuel = k + 1 := ⟨fuel - 1, by omega⟩
    rw [List.length_cons] at hfuel hcap
    show decodeSymbols (fuel' + 1) fixedLitTable fixedDistTable
          ⟨(fixedCodeBits b.toNat ++
              (bs.flatMap (fun b => fixedCodeBits b.toNat))) ++
            (fixedCodeBits 256 ++ rest),
            ((fixedCodeBits b.toNat ++
              (bs.flatMap (fun b => fixedCodeBits b.toNat))) ++
              (fixedCodeBits 256 ++ rest)).length, p⟩ out cap =
        some ((b :: bs).foldl Array.push out,
          ⟨rest, rest.length, p + ((fixedCodeBits b.toNat ++
                (bs.flatMap (fun b => fixedCodeBits b.toNat))).length +
              (fixedCodeBits 256).length)⟩)
    rw [decodeSymbols, List.append_assoc,
      huffDecode_fixedLit b.toNat (by
        have h := UInt8.toNat_lt b; omega) _ p]
    simp only [Option.bind_some]
    rw [if_pos (show b.toNat < 256 by
      have h := UInt8.toNat_lt b; omega)]
    simp only [Nat.toUInt8]
    rw [UInt8.ofNat_toNat,
      Array.size_push, if_neg (show ¬ cap < out.size + 1 by omega),
      ih fuel' (out.push b) _ (by omega) (by rw [Array.size_push]; omega)]
    have hpos : (p + (canonCode fixedLitLengths b.toNat).2) +
          ((bs.flatMap (fun b => fixedCodeBits b.toNat)).length +
            (fixedCodeBits 256).length) =
        p + (((fixedCodeBits b.toNat ++
              (bs.flatMap (fun b => fixedCodeBits b.toNat))).length +
            (fixedCodeBits 256).length)) := by
      rw [List.length_append, fixedCodeBits_length b.toNat,
        fixedCodeBits_length 256]
      omega
    rw [hpos]
    rfl

theorem readBits_one_true (X : List Bool) (p : Nat) :
    readBits 1 ⟨true :: X, (true :: X).length, p⟩ =
      some (1, ⟨X, X.length, p + 1⟩) := rfl

theorem readBits_two_fixed (X : List Bool) (p : Nat) :
    readBits 2 ⟨true :: false :: X, (true :: false :: X).length, p⟩ =
      some (1, ⟨X, X.length, p + 2⟩) := rfl

theorem blocks_fixed (data : List UInt8) (fuel : Nat)
    (out : Array UInt8) (cap : Nat) (rest : List Bool)
    (hcap : out.size + data.length ≤ cap) :
    blocks (fuel + 1)
        ⟨[true, true, false] ++
          ((data.flatMap (fun b => fixedCodeBits b.toNat)) ++
            (fixedCodeBits 256 ++ rest)),
          ([true, true, false] ++
            ((data.flatMap (fun b => fixedCodeBits b.toNat)) ++
              (fixedCodeBits 256 ++ rest))).length, 0⟩ out cap =
      some (data.foldl Array.push out) := by
  have hfuel : data.length <
      ((data.flatMap (fun b => fixedCodeBits b.toNat)) ++
        (fixedCodeBits 256 ++ rest)).length + 1 := by
    rw [List.length_append]
    have hfm := flatMap_fixedCodeBits_length data
    omega
  show blocks (fuel + 1)
      ⟨true :: true :: false ::
        ((data.flatMap (fun b => fixedCodeBits b.toNat)) ++
          (fixedCodeBits 256 ++ rest)),
        (true :: true :: false ::
          ((data.flatMap (fun b => fixedCodeBits b.toNat)) ++
            (fixedCodeBits 256 ++ rest))).length, 0⟩ out cap =
    some (data.foldl Array.push out)
  rw [blocks, readBits_one_true]
  simp only [Option.bind_some]
  rw [readBits_two_fixed]
  simp only [Option.bind_some]
  rw [if_neg (show ¬ ((1 : Nat) = 0) by decide), if_true,
    decodeSymbols_fixedLit data _ out cap _ _ hfuel hcap]
  simp only [Option.bind_some]
  rw [if_true]

theorem byteBits_bitsToByte (x : List Bool) (hx : x.length = 8) :
    byteBits (bitsToByte x) = x := by
  have hlt : valOfBits x < 2 ^ 8 := by
    have h := valOfBits_lt x
    rw [hx] at h
    exact h
  have h2 : ((valOfBits x).toUInt8).toNat = valOfBits x := by
    simp only [Nat.toUInt8]
    exact Nat.mod_eq_of_lt hlt
  show bitsOfNat 8 ((valOfBits x).toUInt8).toNat = x
  rw [h2]
  have h3 := bitsOfNat_valOfBits x 0 8 (by omega)
  rw [h3]
  show x ++ [] = x
  exact List.append_nil x

theorem bytesToBits_packAux (l : List Bool) (n : Nat)
    (hmod : l.length % 8 = 0) (hle : l.length ≤ 8 * n) :
    bytesToBits (packAux n l) = l := by
  induction n generalizing l with
  | zero =>
    have h0 : l.length = 0 := by omega
    have : l = [] := List.eq_nil_of_length_eq_zero h0
    subst this
    rfl
  | succ n ih =>
    cases l with
    | nil => rfl
    | cons b bs =>
      have hge : 8 ≤ (b :: bs).length := by
        have h1 : (b :: bs).length % 8 = 0 := hmod
        have h2 : 0 < (b :: bs).length := by simp
        omega
      have htake : ((b :: bs).take 8).length = 8 := by
        rw [List.length_take]
        omega
      show bytesToBits (bitsToByte ((b :: bs).take 8) ::
        packAux n ((b :: bs).drop 8)) = b :: bs
      rw [bytesToBits_cons, byteBits_bitsToByte _ htake,
        ih ((b :: bs).drop 8) (by rw [List.length_drop]; omega)
          (by rw [List.length_drop]; omega),
        List.take_append_drop]

def writerStream (data : List UInt8) : List Bool :=
  [true, true, false] ++ (data.flatMap (fun b => fixedCodeBits b.toNat)) ++
    fixedCodeBits 256

def padOf (data : List UInt8) : Nat :=
  (8 - (writerStream data).length % 8) % 8

theorem deflateFixed_packAux (data : List UInt8) :
    deflateFixed data = packAux (writerStream data).length
      (writerStream data ++ List.replicate (padOf data) false) := rfl

theorem bytesToBits_deflateFixed (data : List UInt8) :
    bytesToBits (deflateFixed data) =
      writerStream data ++ List.replicate (padOf data) false := by
  rw [deflateFixed_packAux]
  apply bytesToBits_packAux
  · rw [List.length_append, List.length_replicate]
    show ((writerStream data).length +
      (8 - (writerStream data).length % 8) % 8) % 8 = 0
    omega
  · rw [List.length_append, List.length_replicate]
    have hge : 1 ≤ (writerStream data).length := by
      rw [writerStream, List.length_append, List.length_append]
      have h7 : (fixedCodeBits 256).length = 7 := by
        rw [fixedCodeBits_length]
        decide
      simp only [List.length_cons, List.length_nil]
      omega
    have hpad : padOf data ≤ 7 := by
      show (8 - (writerStream data).length % 8) % 8 ≤ 7
      omega
    omega

theorem inflate_deflateFixed (data : List UInt8) (cap : Nat)
    (hcap : data.length ≤ cap) :
    inflate (deflateFixed data) cap = some data := by
  have hstream : writerStream data ++ List.replicate (padOf data) false =
      [true, true, false] ++ ((data.flatMap (fun b => fixedCodeBits b.toNat)) ++
        (fixedCodeBits 256 ++ List.replicate (padOf data) false)) := by
    rw [writerStream, List.append_assoc, List.append_assoc]
  have hfin : (data.foldl Array.push #[]).toList = data := by
    rw [foldl_push_toList]
    rfl
  rw [inflate, bytesToBits_deflateFixed, hstream,
    blocks_fixed data _ #[] cap _ (by
      have h0 : (#[] : Array UInt8).size = 0 := rfl
      omega), Option.map_some, hfin]

end ZipPilot
