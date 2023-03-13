{
  description = "steel-experiments";

  inputs = {
    nixpkgs.url = "github:nixos/nixpkgs/nixos-unstable";
    fstar-src = {
      url = "github:FStarLang/FStar";
      inputs.nixpkgs.follows = "nixpkgs";
    };
    krml-src = {
      url = "github:FStarLang/karamel";
      inputs.fstar.follows = "fstar-src";
      inputs.flake-utils.follows = "fstar-src/flake-utils";
      inputs.nixpkgs.follows = "nixpkgs";
    };
  };

  outputs = inputs@{self, nixpkgs, fstar-src, krml-src}:
    let
      system = "x86_64-linux";
      pkgs = import nixpkgs { inherit system; };
      z3 = fstar-src.packages.${system}.z3;
      fstar = fstar-src.packages.${system}.fstar;
      karamel = krml-src.packages.${system}.karamel;
      steel-experiments = pkgs.clangStdenv.mkDerivation {
        name = "steel-experiments";
        src = ./.;
        enableParallelBuilding = true;
        buildInputs = [ fstar karamel ];
        FSTAR_HOME = fstar;
        KRML_HOME = karamel;
        buildTarget = "lib";
        installPhase = "touch $out";
        #buildPhase = ''
        ##  echo "${fstar}"
        ##  echo "${karamel}"
        ##  make lib -j 1
        ##  make obj/Utils2.fsti.checked
        #'';
      };
    in
    {
      packages.${system} = { inherit steel-experiments; default=steel-experiments; };
      hydraJobs = {
        inherit steel-experiments;
      };
    };
}
