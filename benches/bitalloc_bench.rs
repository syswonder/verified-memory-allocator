use criterion::{black_box, criterion_group, criterion_main, Criterion};
// use testing_allocator::fib::*;
use testing_allocator::original as v1;
use testing_allocator::bitalloc_verus_impl as v2;
use testing_allocator::v3_impl as v3;
pub fn criterion_benchmark(c: &mut Criterion) {
    let mut group = c.benchmark_group("v1v2 fun compare");
    group.bench_function("bitalloc1m_insert", |b| b.iter(|| v2::bitalloc1m_insert()));
    // group.bench_function("bitalloc4k", |b| b.iter(|| v2::bitalloc4k()));
    // group.bench_function("bitalloc_contiguous", |b| b.iter(|| v2::bitalloc_contiguous()));
    // group.bench_function("bitalloc1m", |b| b.iter(|| v2::bitalloc1m()));
    // group.bench_function("bitalloc contiguous", |b| b.iter(|| v1::bitalloc1m()));
    // group.bench_function("v3", |b| b.iter(|| v3::bitalloc1m()));
    group.finish();
}
// 堆代码 duidaima.com
criterion_group!(benches, criterion_benchmark);
criterion_main!(benches);