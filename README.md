<link rel="stylesheet" href="{{site.github.url}}/css/tpp2023.css" charset="utf-8">

# The 19th Theorem Proving and Provers meeting (TPP 2023)

TPP (Theorem Proving and Provers) ミーティングは，
2005年から年に1回開催され，
定理証明系を作っている人から使う側の人まで幅広い人たちが集まり，
様々な側面からの話をしてアイディアの交換をしてきたものです．

ミーティング期間中の討論を大切にしたいと考えていますので，
出来上がった仕事の講演だけでなく，進行中の仕事，未完成の仕事についての講演も歓迎します．
参加者には可能な限りご講演いただくことを期待しています．

TPP is a series of annual meetings for developers as well as users of theorem provers.
Discussions from various aspects and exchanges of ideas have taken place in the past meetings since 2005.

We regard the discussions during the meeting to be most important.
As such, not only the talks about completed work, but those about ongoing 
work and half-baked work are also welcome.
We hope all participants would consider giving a talk.

## 開催日程 / Date
2023年10月30日(月)-31(火) / Mon. 30th to Tue. 31st, October 2023

## 会場 / Venue
東京工業大学・大岡山キャンパス / Tokyo Institute of Technology, Ookayama Campus  
西8号館E棟10階大会議室 / Main Conference Room, 10F, West Bldg. 8E

下記の地図の21の建物です．入り口が3階です，入り口を入って少し進んで, 左側のエレベーターで10階に進んでください．  
Building 21 on the map below. The entrance is on the 3rd floor. Please enter the entrance, go a little further and take the elevator on the left to the 10th floor.  
- [map](https://www.titech.ac.jp/0/maps/ookayama/ookayama)

## 住所 / Address
〒152-8550 東京都目黒区大岡山2-12-1 / 2-12-1 Oookayama, Meguro, Tokyo 152-8550  
[アクセス](https://www.titech.ac.jp/0/maps) / [Access](https://www.titech.ac.jp/english/0/maps)

## 懇親会 / Dinner Party
日時: 10月30日(月) 18:15- / Time: Oct. 30th Mon. 18:15-  
会場 / Place: [ビアバー SHINO](https://tabelog.com/tokyo/A1317/A131711/13116237/) - ([On Google Map](https://maps.app.goo.gl/AJMT7CbDXdEpDJ2i9))  
会費 / Party fee: 学生 / Student 3,000円，一般 / Other 6,000円

## 幹事 / Organizer
中正和久 (山口大学工学部)  
Kazuhisa NAKASHO (Faculty of Engineering, Yamaguchi University)  
Email: nakasho&lt;at&gt;yamaguchi-u.ac.jp  

南出靖彦 (東京工業大学情報理工学院)  
Yasuhiko MINAMIDE (Department of Mathematical and Computing Science, Tokyo Institute of Technology)  
Email: minamide&lt;at&gt;is.titech.ac.jp  

## 参加申し込み / Registration
10/25(水)までに / Please register by 25th October from

<span style="font-size:150%">
[こちらから / here](https://docs.google.com/forms/d/e/1FAIpQLSckyZZlclI_HVj_X7fJ-mMYk1oNFBMZTV2OiB_e1cUks0BkwA/viewform)
</span>

## プログラム / Technical Program
### 10月30日(月) / Oct. 30th (Mon.)
* 12:50 - 13:00 **Opening** (10 min)  

* 13:00 - 13:30 **第一級継続の最適化を行う内在的型安全コンパイル** (30 min)  
  津山 勝輝 @ 東京工業大学  
  継続とはある時点での残りの計算を表す概念である。継続を第一級の値として操作することで、状態・非決定性計算などの計算エフェクトを表現できる。
  そのため、エフェクトハンドラをはじめとして様々な言語機構が継続を操作する仕組みを備えている。
  継続には末尾再開やワンショット継続などの最適化が知られているが、その安全性の機械的証明は存在しない。
  本発表では、継続の使用回数に基づく最適化処理を行い、かつ型保存性を満たすコンパイラの実装に向けた構想を示す。
  これまでに、我々はエフェクトハンドラを持つ言語に対する最適化のない型保存コンパイラを依存型言語であるAgdaで実装した。
  今後は、このコンパイラに継続の使用回数に基づく最適化処理を導入する。
  そのために、ソース言語に多重度と呼ばれる概念を導入することで、継続の使用回数を型レベルでトレースすることを可能にする。

* 13:30 - 14:15 **Leanにおけるモノイダル圏の射の計算** (45 min)  
  水野 勇磨 @ 千葉大学  
  Leanにおいてモノイダル圏の射およびbicategoryの2射を計算する方法を説明する。
  特に、coherece定理をメタプログラミングのレベルで用いることでアソシエーターのつきまとう計算が簡単に行えるようになることを説明する。

* 14:15 - 14:45 **Verifying safety of a MPC/SMC language: the motivation, the progress, and difficulties** (30 min)  
  Greg Weng @ Mercari x 名古屋大学多元数理科学研究科  
  We report on our ongoing efforts of verifying the safety of a MPC/SMC domain-specific language.
  MPC/SMC is a domain focusing on two or more parties collaboratively compute desired results
  without revealing unexpected information during the computation.
  The domain-specific language was designed to abstract the computation but it hasn't been verified formally.
  In this presentation of this unfinished work, the speaker would like to share this project
  which crosses the domain of security and theorem proving, for the motivation, the progress, and difficulties.

* 14:45 - 14:55 **Break** (10 min)

* 14:55 - 15:25 **TBA** (30 min)  
  QI Xuanrui @ 名古屋大学多元数理科学研究科  
  TBA

* 15:25 - 15:55 **TBA** (30 min)  
  才川 隆文 @ 名古屋大学  
  TBA

* 15:55 - 16:25 **Coqによるマッチング理論の形式化** (30 min)  
  辻 陽介 @ 北見工業大学  

* 16:25 - 16:35 **Break** (10 min)

* 16:35 - 17:05 **Environment-friendly monadic equational reasoning for OCaml** (30 min)  
  Jacques Garrigue @ 名古屋大学  
  In order to formally verify OCaml programs,
  we extend a Coq formalization of monadic equational reasoning with a monad to represent typed stores together with its equational theory.
  We combine this result with the output of CoqGen, an experimental compiler from OCaml to Coq, and demonstrate its usefulness with a few examples.

* 17:05 - 17:20 **The Fundamental Theorem of Calculus for the Lebesgue Integral in MathComp-Analysis** (15 min)  
  Reynald Affeldt @ National Institute of Advanced Industrial Science and Technology (AIST)  
  We report on a formalization of the Fundamental Theorem of Calculus
  (FTC) for the Lebesgue integral in the Coq proof assistant.
  Our approach is to formalize Lebesgue's differentiation theorem, of
  which the FTC is a consequence, because it has other applications and
  because its proof can be decomposed in many lemmas and theorems of
  independent interest. As a result, we significantly enrich the theories of
  MathComp-Analysis, a formalization of functional analysis developed on
  top of the Mathematical Components library. This is joint work with Zachary Stone.

* 17:20 - 17:35 **差分プライバシー検証のための関係的ホーア論理の形式化** (15 min)  
  勝股 審也 @ 国立情報学研究所  
  以前、佐藤哲也氏と共同で差分プライバシー検証のための関係的ホーア
  論理の簡便な圏論的意味論を与えた。これをCoqにより形式化している。
  現在、形式化は1. 確率分布間の距離を測るモナド上のダイバージェンス
  の概念を定義し、2. それから圏論的意味論を誘導し、3. その意味論が
  基本定理と呼ばれる性質を満たすことを示している。
  本講演はこの形式化に関して報告する。

* 17:35 - 17:45 **共同利用プロジェクト研究に関するご案内** (10 min)  
  溝口 佳寛 @ 九州大学  

* 17:45 - 17:50 **Closing of Day 1** (5 min)  

### 10月31日(火) / Oct. 31th (Tue.)
* 10:00 - 10:45 **TPPMark** (45 min)  
  中正 和久 @ 山口大学

* 10:45 - 11:15 **簡易な検証器の実装を通じた形式証明の実践講義の可能性** (30 min)  
  Shunsuke Tsuchioka @ 東京工業大学情報理工学院  
  教科書「Type Theory and Formal Proof（Rob NederpeltとHerman Geuvers著, Cambridge University Press）」を、
  「検証器の実装を通じて理解する」という大学院講義を2022年度に東京工業大学情報理工学院において行ったので、
  その経験や教訓、課題や展望について報告する。

* 11:15 - 11:30 **Coq と大規模言語モデルによる定理証明** (15 min)  
  鈴木 彩加 @ 明治大学  
  定理証明支援系Coqの証明を大規模言語モデルに書かせることにより,定理の検証の自動化を目指す.
  具体的には,大規模言語モデルにCoqのスクリプトとその応答を入力とし,
  次のCoqのプログラムを正解の出力として学習させる.
  大規模言語モデルがCoqのプログラムが書けるのか検証する.

* 11:30 - 11:45 **Formalizing λ□ in Lean** (15 min)  
  川添 裕功 @ 東京工業大学 情報理工学院 数理計算科学系  
  本発表ではλ□のLeanによる形式化と強正規化性の証明について述べる。
  λ□は多段階計算機構を備えた言語の基礎をなす体系である。
  今回はλ□の強正規化性を他の強正規化性を持つ体系への変換を用いることで証明した。

* 11:45 - 12:45 **Lunch Break** (10 min)

* 12:45 - 13:15 **計算可能解析学とCoq / Computable Analysis and Coq** (30 min)  
  Holger Thies @ 京都大学 大学院人間・環境学研究科  
  この講演では、Coqを用いた計算可能解析と厳密実数計算の形式的検証に関する現在進行中の研究と、プログラム抽出への応用について紹介します。
  In this talk we present some recent progress on ongoing work on the formalization of computable analysis and exact real computation in Coq and some applications to program extraction.

* 13:15 - 14:00 **Formalizing Life Table in Isabelle/HOL** (45 min)  
  伊藤 洋介 / Yosuke Ito @ ＳＯＭＰＯひまわり生命保険株式会社 / Sompo Himawari Life Insurance Inc.   
  Actuarial Mathematics is a theory in applied mathematics,
  which is mainly used for determining the prices of insurance products
  and evaluating the liability of a company associating with insurance contracts.
  It is related to calculus, probability theory and financial theory, etc.
  In the Archive of Formal Proofs in Isabelle2023,
  I newly formalized the very basic part of Actuarial Mathematics: survival model and life table.
  This formalization is based on the probability theory, and the survival model is developed as generally as possible.
  Such rigorous and general formulation seems very rare; at least I cannot find any similar documentation on the web.

* 14:00 - 14:30 **VASSからVASへの変換の形式化** (30 min)  
  脇坂 勝大 @ 千葉大学大学院 融合理工学府，山本光晴 @ 千葉大学大学院 理学研究院  
  VAS(Vector Addition System)とVASS(Vector Addition System with States)は状態遷移系の一種であり、
  VASSからVASへの到達可能性を保つ変換がHopcroftとPansiotにより示されている。
  本研究では、この変換をMathComp上で形式化しただけでなく、証明に用いられていた条件を一般的なものに拡張した。
  さらにHopcroftらの変換の改良を与え、その最小性も形式化した。

* 14:30 - 14:40 **Break** (10 min)

* 14:40 - 15:10 **スポーツ選手の移籍トレード先決定アルゴリズムのCoq/SSReflectによる検証** (30 min)  
  Kenta Inoue  
  チームスポーツの世界ではチーム同士で選手の移籍トレードを行うことがある。
  このトレードを複数チームで同時に行うときの選手の移籍先決定アルゴリズムについてCoq/SSReflectでの検証する。

* 15:10 - 15:40 **Coqを用いた内在的型付けに基づく確率的プログラミング言語の形式化** (30 min)  
  斉藤 歩夢 @ 東京工業大学 情報理工学院 数理・計算科学系  
  確率的プログラミングは、セキュリティ証明やAIの領域で注目を集めているが、その形式的検証はまだ充分でない。
  特に、依存型の理論における関連研究は、未証明の部分が多く完全でない。
  本研究では、Coqにおける内在的型付け(intrinsically-typed)の新たな方法を提案し、
  サンプリング、スコアリング、および正規化を含む確率的プログラミング言語のCoqによる形式化を行った。
  さらに、この構文の形式化を意味論の形式化へ変換する表示的意味論を定義し、その性質（例えば、let-in構文の可換性）を証明した。
  形式化の応用例として、Bernoulli分布を使用したサンプルプログラムをはじめとする様々なプログラムの結果の正しさを証明した。
  現在は、さまざまな確率分布関数へ対応させるための拡張と、プログラム検証に必要な性質を等式としてライブラリ化することに取り組んでいる。

* 15:40 - 16:10 **Isabelle/HOLによる差分プライバシーの形式化** (30 min)  
  佐藤 哲也 @ 東京工業大学  
  本講演では、差分プライバシーの形式検証のためのIsabelle/HOLライブラリの構成の途中経過を紹介する。
  今回紹介する内容は、(1) 差分プライバシーの基となる統計的距離 (2)ラプラス分布 (3) 差分プライバシーの基本的なメカニズムの形式化 (4) リスト可測空間の位相的圏構造に基づく構成の４つである。

* 16:10 - 16:20 **Closing** (10 min)  

## TPPmark 
解答は中正宛(nakasho&lt;at&gt;yamaguchi-u.ac.jp)にお送りください． / Please send your answer to Nakasho (nakasho&lt;at&gt;yamaguchi-u.ac.jp).

N目並べは碁盤上で行うゲームで，先手と後手の二人のプレイヤーが交互に石を置いていき，
先に縦，横，斜めのいずれかの方向にN個の石を連続して直線上に並べたほうが勝ちです．
以下では，盤面は無限に大きいものとします．
1. N目並べを形式化してください．
2. N目並べでは後手に必勝法がないことを証明してください．
3. Nが十分に大きければ，先手に必勝法がないことを証明してください．
    - ヒント: ペアリング戦略により， N ≧ 9 であれば，先手に必勝法がないことを示せます．
    - 参考文献: [L Győrffy, G Makay, A Pluhár: The pairing strategies of the 9-in-a-row game](https://www.math.u-szeged.hu/~lgyorffy/predok/9_pairings.pdf)

In N-in-a-row game, the first and second players take turns placing stones on a Go board, and the winner being the player who first places its own N stones in a row in either vertical, horizontal, or diagonal direction. In the following, the Go board is assumed to be infinite.
1. Formalize N-in-a-row game.
2. Prove that there is no winning strategy for the second player in N-in-a-row game.
3. Prove that if N is sufficiently large, the first player has no winning strategy.
    - Hint: The pairing strategy shows that if N ≧ 9, then there is no winning strategy for the first player.
    - Reference: [L Győrffy, G Makay, A Pluhár: The pairing strategies of the 9-in-a-row game](https://www.math.u-szeged.hu/~lgyorffy/predok/9_pairings.pdf)

## Mailing List
TPP研究集会はメーリングリストを運営しています．以下の手順でメーリングリストを購読することができます．
1. [Google Group](https://groups.google.com/)にログインします．
1. グループを検索します．
    - 上部の **マイグループ** をクリックし，**すべてのグループとメッセージ** を選択します．
    - 検索ボックスの**グループの名前**に「Theorem Proving and Provers」と入力してEnterキーを押します．
1. 検索リストの「Theorem Proving and Provers」を選択して，**グループへの参加をリクエスト**を押します．

The TPP Meeting manages a mailing list. You can subscribe to the mailing list by following the instructions below:
1. log in to [Google Group](https://groups.google.com/).
1. search for a group.
    - At the top, click **My groups** and select **All groups and messages**.
    - In the search box, type "Theorem Proving and Provers" and press the **Enter** key.
1. Select "Theorem Proving and Provers" in the search list and press **Ask to join group**.

## これまでのTPP / Past TPPs
[TPP2022](https://t6s.github.io/tpp2022/) /
[TPP2021](https://t6s.github.io/tpp2021/) /
[TPP2020](https://aabaa.github.io/tpp2020/) /
[TPP2019](https://akihisayamada.github.io/tpp2019/) /
[TPP2018](https://ksk.github.io/tpp2018/) /
[TPP2017](https://aigarashi.github.io/TPP2017/) /
[TPP2016](http://pllab.is.ocha.ac.jp/~asai/tpp2016/) /
[TPP2015](https://sites.google.com/a/progsci.info.kanagawa-u.ac.jp/tpp2015/) /
[TPP2014](http://imi.kyushu-u.ac.jp/lasm/tpp2014/) /
[TPP2013](http://shirodanuki.cs.shinshu-u.ac.jp/TPP/) /
[TPP2012](http://www.math.s.chiba-u.ac.jp/tpp2012/) /
[TPP2011](http://staff.aist.go.jp/reynald.affeldt/tpp2011/) /
[TPP2010](http://www.math.nagoya-u.ac.jp/~garrigue/tpp10/) /
[TPP2009](http://ist.ksc.kwansei.ac.jp/~ktaka/TPP09/TPP09.html) /
[TPP2008](http://www.score.cs.tsukuba.ac.jp/~minamide/tpp/) /
[TPP2007](http://www.score.cs.tsukuba.ac.jp/~minamide/tpp/tpp07/index.html) /
[TPP2006](http://www.jaist.ac.jp/joint-workshop/TPSmeeting/2006_11/program.html) /
[TPP2005](http://www.jaist.ac.jp/joint-workshop/TPSmeeting/2005_11/program.html)
