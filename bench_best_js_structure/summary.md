| Rank | Variant | Strategy | Verdict |
| :---: | :--- | :--- | :--- |
| 🥇 | **V2: `{ tag: Int, _1, _2 }`** | Monomorphic Object + Int Tag | **Best overall cross-engine target.** 1st in Bun, tied for 1st in Node across patterns. |
| 🥈 | **V5: Flat TypedArrays** | Arena / Struct of Arrays | **Fastest in Node (V8)**, but incurs bounds-check overhead in Bun. Requires manual memory management. |
| 🥉 | **V6: Uniform Class** | Single ES6 Class + Int Tag | Matches V2 in reads, but slower to allocate due to JS class initialization semantics. |
| 4 | **V1: `{ tag: String, ... }`** | Object + String Tag | Surprisingly fast allocator, but pattern-matching strings is 20–30% slower than integers. |
| 5 | **V4: `[tag, _1, _2]` (ReScript)** | Heterogeneous JS Arrays | **Consistently mediocre.** JS Arrays are dynamic vectors, not C tuples. |
| ❌ | **V7 / V8: PureScript** | `instanceof` Prototype Walk | **Disastrous on V8 (2.1x slower).** Linear prototype chain traversal kills traversal speed. |

---

### Key Discoveries & Engine Behavior

#### 1. PureScript’s Compilation Strategy is a Bottleneck (`V7` & `V8`)
Look at the pure traversal numbers (Group 1):
* **Bun:** `V2` takes **6.54 µs** vs `V8`'s **9.01 µs** ($1.38\times$ slower).
* **Node:** `V2` takes **9.64 µs** vs `V8`'s **18.73 µs** ($1.94\times$ slower!).

**Why?**
PureScript tests variants using an `if (v instanceof Constructor)` ladder.
* In V8, `instanceof` is not an $O(1)$ scalar read. It walks the prototype chain (`v.__proto__.__proto__`) and checks identity against the constructor's `.prototype`.
* In a 4-variant ADT, reaching the 4th variant requires up to **4 prototype walks**.
* In contrast, `switch (v.tag)` in **V2** compiles to an indirect jump or jump-table lookup at machine-code level.

> **ES5 vs ES6 PureScript:** Notice that `V7` (ES5 functions) and `V8` (ES6 classes) perform almost identically. Converting `function` to `class` changes nothing because the prototype chain walk is the root cause of the slowdown.

---

#### 2. Why V5 (TypedArray Arena) Wins Node but Loses Bun
* **Node (Traversal):** `V5` takes **8.80 µs** (Fastest).
* **Bun (Traversal):** `V5` takes **8.18 µs** (Loses to V2 at **6.54 µs**).

**The Engine Difference:**
* **V8 (TurboFan):** Excels at hoisting TypedArray bounds checks. TurboFan detects that array reads are safe and converts `arena_tags[id]` directly into raw assembly address offsets: `mov eax, [rdi + rsi]`.
* **Bun (JSC / FTL):** JSC is optimized for pointer-rich object heaps. JSC uses 3D Inline Caching via compact integer **StructureIDs**. Accessing `v._1` on an object with a known StructureID is resolved directly by the FTL JIT compiler without intermediate pointer resolution.

---

#### 3. Why Array Tuples (ReScript / OCaml `V4`) Lag Behind Objects (`V2`)
ReScript targets `[tag, a, b]` for multi-argument constructors. In almost every test on both engines, `V4` is 30% to 40% slower than `V2`.

**Why JS Arrays Are Bad ADTs:**
1. **Double Pointer Indirection:** An object `{ tag: 0, _1: a, _2: b }` stores its fields inline in its JSObject memory chunk. An Array `[0, a, b]` allocates an array wrapper object *plus* an internal pointer to a backing `FixedArray` elements store.
2. **Access Penalty:** Accessing `v[1]` involves checking bounds against `array.length` and dereferencing the elements buffer. Accessing `v._1` reads directly at a fixed offset from the object pointer.
3. **Allocation Overhead:** Allocating `[0, a, b]` asks the memory allocator for two allocations (header + elements store), whereas a simple object literal asks for one.

---

#### 4. The Allocation Anomaly (Benchmark 3)
Notice who won Construction & Allocation in Bun:
* **Winner:** `V1: Object + String Tag` (**4.46 µs**) and `V5` (**4.46 µs**).
* **Why did String Tag beat Int Tag?**
  In JavaScript engines (particularly JSC), small string literals like `"add"`, `"mul"`, and `"succ"` are **interned atoms**. When JSC compiles `{ tag: "add", _1: a, _2: b }`, it generates an optimized bump-pointer object allocation with a pre-interned string pointer already baked into the template, making the allocation essentially as fast as a TypedArray pointer bump.

---

### Compiler Design Recommendations

If you are designing a backend compiler (e.g., for Lean, Elm, or a custom functional language targeting JS):

1. **Default to Monomorphic Object Literals with Integer Tags (`V2`):**
   ```javascript
   // Define a uniform shape so all instances share ONE hidden class (Map/StructureID)
   const add  = (a, b) => ({ tag: 0, _1: a, _2: b });
   const mul  = (a, b) => ({ tag: 1, _1: a, _2: b });
   const succ = a      => ({ tag: 2, _1: a, _2: null }); // explicitly keep 2 fields!
   const zero =           ({ tag: 3, _1: null, _2: null });
   ```
   *Padding unused properties with `null` guarantees a single hidden class for all variants of that ADT.*

2. **Avoid PureScript's `instanceof` Pattern Matching:**
   Compiling ADTs to distinct classes with `instanceof` matching incurs a ~2x performance penalty on V8 compared to a tag switch.

3. **Avoid Array Tuples (`[tag, ...args]`):**
   Unless you need array indexing via dynamic offsets, array-based ADTs introduce unneeded indirection and array metadata overhead.

4. **Reserve Flat Arenas (`V5`) for Hot Computational Kernels:**
   TypedArrays eliminate GC pressure entirely and provide peak performance on Node/V8, but at the expense of manual memory management and worse developer ergonomics.
