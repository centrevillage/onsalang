# voice_host

仕様 §17.5 の例: `dsp.onsa` の flow `voice`（`@export`）を静的ライブラリにし、C のホスト `host.c` から呼ぶ。
`./build.sh` が `onsa build --target host` で C を出して `cc` でまとめ、1 秒の音を `out.wav` に書く。

`onsa.toml` の `daisy` のターゲットは §17.5 の例の形のまま置いてある。
その `fp = "strict-ftz"`・`main_frame = "static"` と、クロスの `platform` の `staticlib` は、この版のコンパイラが対応しない値で、§15.3 により `onsa build --target daisy` は E0200 になる。
