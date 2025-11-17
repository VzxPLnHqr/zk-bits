{
  description = "A Nix-flake-based Scala development environment";
  
  inputs.nixpkgs.url = "github:nixos/nixpkgs/nixos-unstable";
  outputs = { self, nixpkgs }:
    let
      javaVersion = 17; # Change this value to update the whole stack

      supportedSystems = [ "x86_64-linux" "aarch64-linux" "x86_64-darwin" "aarch64-darwin" ];
      forEachSupportedSystem = f: nixpkgs.lib.genAttrs supportedSystems (system: f {
        pkgs = import nixpkgs { inherit system; overlays = [ self.overlays.default ]; };
      });


    in
    {
      overlays.default = final: prev:
        let
          jdk = prev."jdk${toString javaVersion}";
        in
        {
          sbt = prev.sbt.override { jre = jdk; };
          scala = prev.scala_3.override { jre = jdk; };
        };

      devShells = forEachSupportedSystem ({ pkgs }: {
        default = pkgs.mkShell {
          buildInputs = with pkgs; [
            stdenv
            sbt
            openjdk
            boehmgc
            libunwind
            clang
            zlib
            secp256k1
            nodejs
            yarn 
            just
            fish
          ];
          packages = with pkgs; [ 
            scala 
            sbt 
            coursier 
            scala-cli 
          ];

          # Only exec into fish for interactive shells, not during `nix develop --command`
          shellHook = ''
            # If the shell is interactive (PS1 is set), and not already inside fish, switch to fish
            if [ -n "$PS1" ] && command -v fish >/dev/null 2>&1 && [ -z "$INSIDE_FISH" ]; then
              exec fish
            fi
          '';
          
        };
      });
    };
}
