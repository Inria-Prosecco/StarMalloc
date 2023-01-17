{
  description = "steel-experiments";

  inputs = {
    nixpkgs.follows = "hacl-nix/nixpkgs";
    hacl-nix.url = "github:hacl-star/hacl-nix";
  };

  outputs = inputs@{self, nixpkgs, hacl-nix}:
    let
      system = "x86_64-linux";
      pkgs = import nixpkgs { inherit system; };
      haclpkgs = hacl-nix.packages.${system};
      steel-experiments = pkgs.stdenv.mkDerivation {
        name = "steel-experiments";
        src = ./.;
        enableParallelBuilding = true;
        #buildInputs = [ haclpkgs.fstar haclpkgs.karamel ];
        FSTAR_HOME = haclpkgs.fstar;
        KRML_HOME = haclpkgs.karamel;
        buildTarget = "verify";
        #buildPhase = ''
        #  make verify
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
