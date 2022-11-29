import data.real.basic


lemma mp (p q : Prop) :
  p → (p → q) → q := 
λ hp hpq, hpq hp






