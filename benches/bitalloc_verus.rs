use criterion::{black_box, criterion_group, criterion_main, Criterion};
use testing_allocator::fib::*;
use testing_allocator::bitalloc_verus_impl::{bitalloc16,bitalloc4k,bitalloc_contiguous};
pub fn criterion_benchmark(c: &mut Criterion) {
    // let mut group = c.benchmark_group("My Group");
    // group.bench_function("Function 1", |b| b.iter(|| fibonacci1(black_box(20))));
    // group.bench_function("Function 2", |b| b.iter(|| fibonacci2(black_box(20))));
    // group.finish();

    // c.bench_function("bitalloc16", |b| b.iter(|| bitalloc16()));

    let mut group = c.benchmark_group("Bitmap allocator Verus");
    group.bench_function("bitalloc16", |b| b.iter(|| bitalloc16()));
    group.bench_function("bitalloc4k", |b| b.iter(|| bitalloc4k()));
    group.bench_function("bitalloc_contiguous", |b| b.iter(|| bitalloc_contiguous()));
    group.finish();
}
// 堆代码 duidaima.com
criterion_group!(benches, criterion_benchmark);
criterion_main!(benches);