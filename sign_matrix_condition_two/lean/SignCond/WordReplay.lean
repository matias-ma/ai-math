import SignCond.WordMain

namespace SignCond.FiniteWord

/-- Spread the bits of a mask into radix slots. The checker verifies the resulting words. -/
private def spreadSteps (w q : ℕ) : ℕ → ℕ → ℕ
  | 0,x => x
  | k+1,x =>
    let half := 2^k
    let low := (2^half-1)*((2^(w*2^q)-1)/(2^(2*w*half)-1))
    spreadSteps w q k ((x &&& low) ||| ((x &&& (low <<< half)) <<< (half*(w-1))))

def makeRow (w q x y : ℕ) : Row := ⟨spreadSteps w q q x,spreadSteps w q q y⟩

/-- Separate the positive and negative parts of the signed coefficient word. Both
parts and the modular identity are checked by the premises of wordWitness. -/
def outputWords (j : ℕ) (A B C D : Row) (s μ p w v : ℕ) : ℕ × ℕ :=
  let base := 2^w
  let mask := ones base j
  let bias := 2^v
  let cap := bias-1
  let modulus := base^j-1
  let q := quadCode A B C D j base s μ
  let shifted := (((q : ZMod modulus)^(2^p)) + ((bias*mask:ℕ) : ZMod modulus)).val
  let above := (shifted >>> v) &&& mask
  let low := shifted &&& (cap*mask)
  let positive := low &&& (cap*above)
  (positive, bias*(mask-above) - (low-positive))

end SignCond.FiniteWord
