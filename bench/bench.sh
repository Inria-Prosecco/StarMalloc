echo "C"
time ./bench/a.out 1000000
echo "C++"
time ./bench/cpp.a.out 1000000
echo "OCaml"
time ./bench/ocaml.a.out -n 1000000
