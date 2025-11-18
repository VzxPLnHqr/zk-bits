## zk-bits

Because sometimes to understand something you have to explain it to a computer first.

This is an attempt to build up some intuition for non-interactive zero knowledge
proofs, from first principles.

```
$ nix develop --command scala-cli run . --offline --main-class zk.Demo
Compiling project (Scala 3.6.4, JVM (21))
Compiled project (Scala 3.6.4, JVM (21))

==== Bit Commitment OR‑Proof Demonstration ====

Bit=0 → Commitment=85034715730534986616082764807045738054386085633783001827211092758699191394930
Verified=true

Bit=1 → Commitment=41983687818014014158380859053252414321887708302227815910930333578783270363042
Verified=true

Tampered commitment → Verification: false
```