# 電信振替仕様

## 仕様

- 二人の口座保持者 alice と bob が存在する
- どちらの口座残高も初期値は 5
- 合計残高は初期時点で 10
- 同一の送金処理「Wire」を実行する 2 個のプロセスが並行に一度だけ走る
- 各プロセスは alice→bob への送金を試行する
- 取引は同一プロセス内でラベル単位で原子的に実行され、プロセス間の実行順序は非決定的であり、相互に割り込み（インターリーブ）が起こり得る。


## 変数と初期化

- 集合 people = {"alice","bob"}
- 口座残高写像 acc は acc["alice"] = 5、acc["bob"] = 5 で初期化
- グローバル変数 inflight = 0（予約済みで未入金の送金中資金を表す）
- 各プロセスには局所変数がある：
  - sender = "alice"（送金元は固定）
  - receiver = "bob"（送金先は固定）
  - amount ∈ 1..acc[sender]（開始時の alice 残高の範囲から非決定的に 1 以上の整数を一つ選ぶ）

## 操作

- Reserve（予約）
  - amount <= acc[sender] の場合、`acc[sender] := acc[sender] - amount; inflight := inflight + amount` を原子的に実行する。
- Deposit（入金）
  - `acc[receiver] := acc[receiver] + amount; inflight := inflight - amount` を原子的に実行する。
- Refund（返金／ロック解除）
  - 分散システムの一部（送金先側の入金処理系など）が復旧不可能になった場合、予約済み資金をロック解除し、`acc[sender] := acc[sender] + amount; inflight := inflight - amount` を原子的に実行する。
  - Refund は Reserve の後に Deposit の代替として常に選択可能であり、いずれかで必ず処理を終える。

## 性質

- 「全ての人物 p について acc[p] ≥ 0」。すなわち残高がマイナスにならない。
- 「inflight ≥ 0」。
- 「acc["alice"] + acc["bob"] + inflight = 10」。
  - サービスが停止して Deposit が永遠に実行されなくても、資金は `inflight` に保持され、消失しない。
- 「全プロセスが完了したとき inflight = 0」。
  - 形式的には `NoInflightAtAllDone == (\A self \in DOMAIN pc: pc[self] = "Done") => inflight = 0` を不変条件として追加する。
  - 復旧不可能な障害が生じた場合でも Refund によりロックは解除され、資金が宙ぶらりんにならない。
