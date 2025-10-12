# 電信振替仕様

## 仕様

- 二人の口座保持者 alice と bob が存在する
- どちらの口座残高も初期値は 5
- 合計残高は初期時点で 10
- 同一の送金処理「Wire」を実行する 2 個のプロセスが並行に一度だけ走る
- 各プロセスは alice→bob への送金を試行する
- 取引は同一プロセス内で原子的に連続するが、プロセス間の実行順序は非決定的であり、相互に割り込み（インターリーブ）が起こり得る。


## 変数と初期化

- 集合 people = {"alice","bob"}
- 口座残高写像 acc は acc["alice"] = 5、acc["bob"] = 5 で初期化
- 各プロセスには局所変数がある：
  - sender = "alice"（送金元は固定）
  - receiver = "bob"（送金先は固定）
  - amount ∈ 1..acc[sender]（開始時の alice 残高の範囲から非決定的に 1 以上の整数を一つ選ぶ）

## 操作

- Deposit
  - acc[receiver] := acc[receiver] + amount を行う。
- Withdraw
  - acc[sender] := acc[sender] - amount

## 性質

- 「全ての人物 p について acc[p] ≥ 0」。すなわち残高がマイナスにならない。
- 「やがて常に acc["alice"] + acc["bob"] = 10 が成り立つ」
   - 本来は: 「常に acc["alice"] + acc["bob"] = 10 が成り立つ」 にしたい
