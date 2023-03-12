# Steel Experiments

Some experiments as a F*/Steel beginner.

## StarMalloc

- `make test-slab`: small slab allocator test
- `make test-mmap`: small large allocator (AVL+mmap) test
- `make test-both`: small allocator test
- `make lib`: `bench/starmalloc.so` compilation

Working with quite complicated programs (e.g. zathura, a PDF viewer)... when compiled with clang
