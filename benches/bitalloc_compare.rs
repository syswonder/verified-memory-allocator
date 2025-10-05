use criterion::{BenchmarkId, Criterion, criterion_group, criterion_main};

use hvisor_ma::v_original::v1_impl as v1; // 版本1（原有实现）
use hvisor_ma::v_verus::v2_impl as v2; // 版本2（如：Verus版本清理后的纯 exec 实现）
use hvisor_ma::v_verus::v3_impl as v3;

// pub fn criterion_benchmark(c: &mut Criterion) {
//     let mut group = c.benchmark_group("Bitmap allocator");
//     // group.bench_function("bitalloc16", |b| b.iter(|| v1::bitalloc16()));
//     // group.bench_function("bitalloc4k", |b| b.iter(|| v1::bitalloc4k()));
//     // group.bench_function("bitalloc_contiguous", |b| b.iter(|| v1::bitalloc_contiguous()));

//     group.bench_function("bitalloc16", |b| b.iter(|| v2::bitalloc16()));
//     group.bench_function("bitalloc4k", |b| b.iter(|| v2::bitalloc4k()));
//     group.bench_function("bitalloc_contiguous", |b| b.iter(|| v2::bitalloc_contiguous()));

//     group.finish();
// }

// fn bench_bitalloc16(c: &mut Criterion) {
//     let mut group = c.benchmark_group("bitalloc16-compare");

//     group.bench_function(BenchmarkId::new("v1", "16"), |b| b.iter(|| v1::bitalloc16()));
//     group.bench_function(BenchmarkId::new("v2", "16"), |b| b.iter(|| v2::bitalloc16()));

//     group.finish();
// }

// fn bench_bitalloc4k(c: &mut Criterion) {
//     let mut group = c.benchmark_group("bitalloc4k-compare");

//     group.bench_function(BenchmarkId::new("v1", "4k"), |b| b.iter(|| v1::bitalloc4k()));
//     group.bench_function(BenchmarkId::new("v2", "4k"), |b| b.iter(|| v2::bitalloc4k()));

//     group.finish();
// }

fn bench_contiguous(c: &mut Criterion) {
    let mut group = c.benchmark_group("bitalloc-contiguous-compare");

    group.bench_function(BenchmarkId::new("v1", "contig"), |b| {
        b.iter(|| v1::bitalloc_contiguous())
    });
    group.bench_function(BenchmarkId::new("v2", "contig"), |b| {
        b.iter(|| v2::bitalloc_contiguous())
    });
    group.bench_function(BenchmarkId::new("v3", "contig"), |b| {
        b.iter(|| v3::bitalloc_contiguous())
    });

    group.finish();
}

criterion_group!(benches, bench_contiguous);
criterion_main!(benches);
