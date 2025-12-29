use criterion::{black_box, criterion_group, criterion_main, Criterion};
// use testing_allocator::fib::*;
use testing_allocator::original as v1;
use testing_allocator::bitalloc_verus_impl as v2;
use testing_allocator::v3_impl as v3;
use testing_allocator::v4_impl as v4;

pub fn criterion_benchmark(c: &mut Criterion) {
    let mut group = c.benchmark_group("func_vs");
    // group.bench_function("bitalloc_16", |b| b.iter(|| v4::bitalloc16()));
    // group.bench_function("bitalloc_4k", |b| b.iter(|| v4::bitalloc4k()));
    group.bench_function("bitalloc_contiguous", |b| b.iter(|| v4::bitalloc_contiguous()));
    // group.bench_function("bitalloc1m_alloc", |b| b.iter(|| v2::bitalloc1m_alloc_contiguous()));
    // group.bench_function("bitalloc contiguous", |b| b.iter(|| v1::bitalloc1m()));
    // group.bench_function("v3", |b| b.iter(|| v3::bitalloc1m()));
    // group.bench_function("alloc_wrapper", |b| {
    //     b.iter_batched(
    //         // ---------- setup 阶段：构造随机 ba，不计时 ----------
    //         || v4::bitalloc1m_new(),

    //         // ---------- measurement 阶段：只对这一块计时 ----------
    //         // |ba| {
    //         //     // 调用你的包装函数，而不是直接 ba.alloc()
    //         //     let _ = black_box(v4::bitalloc1m_alloc(ba));
    //         // },
    //         |ba| {
    //         // 把参数包一层 black_box，防止被优化
    //             v4::bitalloc1m_alloc(ba);
    //         },

    //         criterion::BatchSize::SmallInput,
    //     );
    // });
    // group.bench_function("bitalloc1m_alloc", |b| b.iter(|| v4::bitalloc1m_alloc()));
    group.finish();
}
// 堆代码 duidaima.com
criterion_group!(benches, criterion_benchmark);
criterion_main!(benches);