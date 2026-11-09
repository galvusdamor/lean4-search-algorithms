import SearchAlgorithms.HeuristicCache

/-!
# Micro-benchmark: what a cache lookup costs

`SearchAlgorithms.HeuristicCache` offers three caches for a pure function.  They differ only
in run time — all three are *proved* to be the function they cache — so the choice is made by
measurement.  This program measures the cost of a single lookup by performing a million of
them on a cache of ten thousand entries (the cached function itself is trivial, so what is
measured is the cache and nothing else).

```
lake exe benchmemo            -- one million lookups of each kind
lake exe benchmemo 10000000   -- ... with a different number of lookups
```

## Measured (8-core x86-64 Linux, ten thousand distinct arguments)

| lookup | ns per call |
|---|---|
| no cache (the function itself, trivial) | 14 |
| `CachedFun.ofArray` (flat array of thunks) | 24 |
| `CachedFun.ofChunked` (chunks of 1024 thunks, allocated on demand) | 36 |
| `CachedFun.ofWTrie` (16-way trie, 4 levels) | 175 |
| `CachedFun.ofTrie` (binary trie, 14 levels) | 330 |

So the flat array and the chunked cache are essentially free, while the tries cost a few
hundred nanoseconds — which is what buys them their memory behaviour: a trie allocates only
for the vertices that are actually looked at, the chunked cache only for the chunks that are
touched, and the flat array one cell per vertex up front.  All of them are negligible next to
an expensive heuristic (`BenchCache` measures the whole search).  Run-to-run variation is
about ±20 %.
-/

open SearchAlgorithms

/-- A trivial "heuristic": what is measured is the cache around it, not the function. -/
def memoFun (n : ℕ) : ℕ∞ := (n % 97 : ℕ)

/-- Add up `n` lookups spread over ten thousand distinct arguments. -/
def memoLoop (g : ℕ → ℕ∞) (n : ℕ) : ℕ :=
  Id.run do
    let mut acc := 0
    for i in [0:n] do
      acc := acc + ((g ((i * 7919) % 10000)).getD 0)
    return acc

def memoTime (label : String) (n : ℕ) (act : Unit → ℕ) : IO Unit := do
  let t0 ← IO.monoNanosNow
  let r := act ()
  if r == 0 then IO.println "(zero)" else pure ()
  let t1 ← IO.monoNanosNow
  let ns := t1 - t0
  IO.println s!"  {label}: {ns / 1000000} ms ({ns / 1000} µs), {ns / max n 1} ns per lookup"
  (← IO.getStdout).flush

def main (args : List String) : IO Unit := do
  let n := match args with
    | [s] => s.toNat?.getD 1000000
    | _ => 1000000
  IO.println s!"{n} lookups on a cache of 10000 entries"
  memoTime "no cache" n (fun _ => memoLoop memoFun n)
  memoTime "array   " n (fun _ => memoLoop (CachedFun.ofArray 10000 VIndex.ofNat memoFun).fn n)
  memoTime "chunked " n (fun _ => memoLoop (CachedFun.ofChunked 1024 16 VIndex.ofNat memoFun).fn n)
  memoTime "wtrie   " n (fun _ => memoLoop (CachedFun.ofWTrie VIndex.ofNat 16 memoFun).fn n)
  memoTime "trie    " n (fun _ => memoLoop (CachedFun.ofTrie VIndex.ofNat 64 memoFun).fn n)
