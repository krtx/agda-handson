# 環境設定

このハンズオンでは、以下のソフトウェアが必要です。

- Agda >= 2.5
- Agda の標準ライブラリ >= 0.12
- Emacs

これらを手元の環境にインストールするか、Docker イメージを用意したので、そちらを利用してください。

## エディタについて

Atom や Vim でもできるようです。

- Atom
  - https://atom.io/packages/agda-mode
- Vim
  - https://github.com/derekelkins/agda-vim

## Dockerを使う場合

[krtx/docker-agda](https://hub.docker.com/r/krtx/docker-agda/) には以下のソフトウェアが含まれています。

- Agda 2.5.1.1
- Agda の標準ライブラリ 0.12
- Emacs

```
$ docker pull krtx/docker-agda
$ AGDA_HANDSON=agda-handsonをインストールしたディレクトリ
$ docker run -v $AGDA_HANDSON:/root/agda-handson -it krtx/docker-agda emacs
```

## ローカルにインストールする場合

### Stackをインストール

```
$ curl -L https://get.haskellstack.org | sh
$ stack setup
```

cf. [Stackのドキュメント](https://docs.haskellstack.org/en/stable/README/)

### Agdaをインストール

```
$ stack install Agda # 1時間くらい
```

### 標準ライブラリをインストール

`$HOME/.agda` 以下に標準ライブラリをインストールします。

```
$ ./install-stdlib.sh
```

cf. [Agdaのパッケージ管理システム](https://agda.readthedocs.io/en/latest/tools/package-system.html)

### Emacsをインストール

表示が崩れる可能性があるので、ウィンドウモード推奨です。

Macでhomebrewを使う場合

```
$ brew install --with-cocoa --srgb emacs
```

### Emacsの設定

以下を追記

```
(load-file (let ((coding-system-for-read 'utf-8))
             (shell-command-to-string "agda-mode locate")))
```

日本語キーボードで￥を打ってagdaの入力モードにならなかったらIMEの設定を確認し以下を追記

```
(define-key global-map [?¥] [?\\])
```

# 確認

TODO: write
