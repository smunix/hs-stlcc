{
  inputs = {
    # nixpkgs.url = "github:cachix/devenv-nixpkgs/rolling";
    nixpkgs.url = "github:nixos/nixpkgs?ref=master";
    systems.url = "github:nix-systems/default";
    devenv.url = "github:cachix/devenv";
    devenv.inputs.nixpkgs.follows = "nixpkgs";
    nix-utils.url = "github:smunix/nix-utils";
    nix-utils.inputs.nix-filter.follows = "nix-filter";
    nix-utils.inputs.nixpkgs.follows = "nixpkgs";
    nix-filter.url = "github:numtide/nix-filter";
    # bluefin.url = "github:smunix/bluefin?ref=01-compile-nix";
    bluefin.url = "github:tomjaguarpaw/bluefin?ref=master";
    bluefin.flake = false;
    ghcitui.url = "https://github.com/CrystalSplitter/ghcitui";
    ghcitui.flake = false;
  };

  nixConfig = {
    extra-trusted-public-keys =
      "devenv.cachix.org-1:w1cLUi8dv3hnoSPGAuibQv+f9TZLr6cv/Hm9XgU50cw=";
    extra-substituters = "https://devenv.cachix.org";
  };

  outputs = { self, nixpkgs, devenv, systems, ... }@inputs:
    with inputs.nix-utils.lib;
    with inputs.nix-filter.lib;
    let forEachSystem = nixpkgs.lib.genAttrs (import systems);
    in {
      packages = forEachSystem (system: {
        devenv-up = self.devShells.${system}.default.config.procfileScript;
      });

      devShells = forEachSystem (system:
        let
          pkgs = nixpkgs.legacyPackages.${system};
          hpkgs = fast pkgs.haskell.packages.ghc98 [{
            modifiers = with pkgs.haskell.lib; [ disableLibraryProfiling ];
            extension = with pkgs.haskell.lib;
              hf: hp:
              with hf; {
                bluefin-internal = overrideCabal
                  (callCabal2nix "bluefin-internal" (filter {
                    root = "${inputs.bluefin}/bluefin-internal";
                    exclude = [ ];
                  }) { }) {
                    postPatch = with pkgs; ''
                      ${rsync}/bin/rsync -avz ${inputs.bluefin}/LICENSE .
                    '';
                  };
                bluefin = overrideCabal (callCabal2nix "bluefin" (filter {
                  root = "${inputs.bluefin}/bluefin";
                  exclude = [ ];
                }) { }) {
                  postPatch = with pkgs; ''
                    ${rsync}/bin/rsync -avz ${inputs.bluefin}/LICENSE .
                  '';
                };
                gtui = callCabal2nix "gtui" (filter {
                  root = inputs.ghcitui;
                  exclude = [ ];
                }) { };
                hs-stlcc = callCabal2nix "hs-stlcc" (filter {
                  root = inputs.self;
                  exclude = [ (matchExt "cabal") ];
                }) { };
              };
          }];
        in {
          default = devenv.lib.mkShell {
            inherit inputs pkgs;
            modules = [{
              # https://devenv.sh/reference/options/
              packages = with hpkgs;
                with pkgs; [
                  fourmolu
                  git
                  (ghcWithPackages (p:
                    with p; [
                      cabal-install
                      ghcid
                      # gtui
                      # ghclive
                      haskell-language-server
                      hpack
                      implicit-hie
                      hs-stlcc
                    ]))
                ];

              enterShell = ''
                git --version
                hpack --version
                hpack --force package.yaml
                gen-hie --cabal &> hie.yaml
              '';

              processes.run.exec = "hello";

              scripts = {
                loop.exec = "ghcid -W -a -c cabal repl lib:hs-stlcc";
              };

              pre-commit.hooks = {
                fourmolu.enable = true;
                stylish-haskell.enable = true;
                nixfmt.enable = true;
              };
            }];
          };
        });
    };
}
