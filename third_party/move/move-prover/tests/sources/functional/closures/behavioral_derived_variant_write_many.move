// Copyright © Aptos Foundation
// SPDX-License-Identifier: Apache-2.0

// A sequence of derived writes to fields of a wide enum variant: each write
// updates one field of the variant.
module 0x42::hof {
    public fun apply_to<T>(s: &mut T, f: |&mut T|) { f(s) }
    spec apply_to {
        pragma opaque;
        requires requires_of<f>(s);
        aborts_if aborts_of<f>(s);
        ensures ensures_of<f>(old(s), s);
    }
}

module 0x42::many {
    use 0x42::hof::apply_to;
    enum S has copy, drop, store {
        V { f1: u64, f2: u64, f3: u64, f4: u64, f5: u64, f6: u64, f7: u64, f8: u64, f9: u64, f10: u64, f11: u64, f12: u64 }
    }
    enum M has copy, drop, store {
        A { a1: u64, a2: u64, a3: u64, a4: u64, a5: u64, a6: u64, p: u64 },
        B { a6: u64, a5: u64, a4: u64, a3: u64, a2: u64, a1: u64 }
    }

    public fun set_many(x: &mut S) { x.f1 = 1; x.f2 = 2; x.f1 = 3; x.f3 = 4 }
    public fun set_shared(x: &mut M) { x.a1 = 1; x.a2 = 2; x.a3 = 3 }

    fun c_many(s: &mut S) { apply_to(s, set_many) }
    spec c_many {
        aborts_if false;
        ensures s.f1 == 3 && s.f2 == 2 && s.f3 == 4;
        ensures s.f4 == old(s.f4) && s.f5 == old(s.f5) && s.f6 == old(s.f6) && s.f7 == old(s.f7);
        ensures s.f8 == old(s.f8) && s.f9 == old(s.f9) && s.f10 == old(s.f10) && s.f11 == old(s.f11);
        ensures s.f12 == old(s.f12);
    }
    fun c_many_incorrect(s: &mut S) { apply_to(s, set_many) }
    spec c_many_incorrect { ensures s.f1 == 1; }

    fun c_shared(s: &mut M) { apply_to(s, set_shared) }
    spec c_shared {
        aborts_if false;
        ensures (old(s) is A) == (s is A);
        ensures s.a1 == 1 && s.a2 == 2 && s.a3 == 3;
        ensures s.a4 == old(s.a4) && s.a5 == old(s.a5) && s.a6 == old(s.a6);
        ensures (old(s) is A) ==> s.p == old(s.p);
    }
    fun c_shared_incorrect(s: &mut M) { apply_to(s, set_shared) }
    spec c_shared_incorrect { ensures s is A; }
}

// exclude_for: lean
// The Lean backend does not verify the higher-order function `apply_to` itself.
