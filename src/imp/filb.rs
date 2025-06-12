// use vstd::prelude::*;

// verus! {
//     fn fibo_impl(n: u64) -> u64 {
//         // requires(fibo_fits_u64(n));
//         // ensures(|result: u64| result == fibo(n));

//         if n == 0 { return 0; }

//         let mut prev: u64 = 0;
//         let mut cur: u64 = 1;
//         let mut i: u64 = 1;

//         while i < n {
//             // invariant([
//             //     0 < i && i <= n,
//             //     fibo_fits_u64(n as nat),
//             //     fibo_fits_u64(i as nat),
//             //     cur == fibo(i),
//             //     prev == fibo(i as nat - 1),
//             // ]);
//             let new_cur = cur + prev;
//             prev = cur;
//             cur = new_cur;
//             // assert(prev == fibo(i as nat));
//             i = i + 1;
//             // lemma_fibo_is_monotonic(i, n);
//             }
//         cur
//     }
// }

#[test]
fn test_not() {
    println!("{}", !0);
}

fn main() {
    println!("{:b}", !0);
}
