{
  description = "steel-experiments";

  inputs = {
    nixpkgs.url = "github:nixos/nixpkgs/nixos-unstable";
    fstar-src = {
      url = "github:FStarLang/FStar";
      inputs.nixpkgs.follows = "nixpkgs";
    };
    steel-src = {
      url = "github:FStarLang/steel";
      inputs.nixpkgs.follows = "nixpkgs";
      inputs.flake-utils.follows = "fstar-src/flake-utils";
      inputs.fstar.follows = "fstar-src";
    };
    krml-src = {
      url = "github:FStarLang/karamel";
      inputs.nixpkgs.follows = "nixpkgs";
      inputs.flake-utils.follows = "fstar-src/flake-utils";
      inputs.fstar.follows = "fstar-src";
    };
  };

  outputs = inputs@{self, nixpkgs, fstar-src, krml-src, steel-src}:
    let
      system = "x86_64-linux";
      pkgs = import nixpkgs { inherit system; };
      inherit (pkgs) lib;
      z3 = fstar-src.packages.${system}.z3;
      fstar = fstar-src.packages.${system}.fstar;
      steel = steel-src.packages.${system}.steel;
      karamel = krml-src.packages.${system}.karamel.home;

      # allocator derivation
      # TODO: use pkgs.llvmPackages_latest.stdenv.mkDerivation
      # currently, there is some linking issue, try to fix it/report it
      starmalloc = pkgs.stdenv.mkDerivation {
        name = "steel-experiments";
        src = lib.sourceByRegex ./. [
          "lib_avl_common(/.*)?"
          "lib_avl_mono(/.*)?"
          "lib_bitmap(/.*)?"
          "lib_list(/.*)?"
          "lib_misc(/.*)?"
          "lib_ringbuffer(/.*)?"
          "src(/.*)?"
          "c(/.*)?"
          "Makefile.include"
          "Makefile"
        ];
        enableParallelBuilding = true;
        buildInputs = [ fstar steel karamel pkgs.removeReferencesTo ];
        FSTAR_HOME = fstar;
        STEEL_HOME = steel;
        KRML_HOME = karamel;
        installPhase = "mkdir $out && cp -r dist out/*.so $out";
        buildFlags = [ "lib" "hardened_lib" ];
        postInstall = ''
          find dist -type f -name "*" -exec remove-references-to -t ${karamel} {} \;
        '';
      };
    in
    {
      packages.${system} = {
        inherit starmalloc;
        default=starmalloc;
      };
    };
}
