-- lemmas not in currently used version of mathlib that will be added in the future

import Mathlib.Order.Interval.Finset.Fin
import Mathlib.Data.Vector.Basic

variable {α β : Type*} {n : ℕ}
open List (Vector)
open Fintype
open Finset
open Fin


@[simp] theorem map_valEmbedding_univ :
    (Finset.univ : Finset (Fin n)).map Fin.valEmbedding = Iio n := by
  ext
  simp [orderIsoSubtype.symm.surjective.exists, OrderIso.symm]

theorem Fin.card_filter_val_lt {m : ℕ} : #{i : Fin n | i < m} = min n m := by
  simp [← card_map valEmbedding, ← filter_filter, exists_iff, map_filter']
