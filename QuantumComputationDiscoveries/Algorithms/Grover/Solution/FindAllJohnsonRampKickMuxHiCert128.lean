/-
Copyright 2026 Google LLC

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-/
module

public import QuantumComputationDiscoveries.Algorithms.Grover.Solution.FindAllJohnsonRampKickMuxEval
public import QuantumComputationDiscoveries.Algorithms.Grover.Solution.FindAllJohnsonRampKickMuxHiBase
public import QuantumComputationDiscoveries.Algorithms.Grover.Solution.FindAllJohnsonRampKickMuxHi128T0
public import QuantumComputationDiscoveries.Algorithms.Grover.Solution.FindAllJohnsonRampKickMuxHi128T1
public import QuantumComputationDiscoveries.Algorithms.Grover.Solution.FindAllJohnsonRampKickMuxHi128T2
public import QuantumComputationDiscoveries.Algorithms.Grover.Solution.FindAllJohnsonRampKickMuxHi128T3
public import QuantumComputationDiscoveries.Algorithms.Grover.Solution.FindAllJohnsonRampKickMuxHi128T4
public import QuantumComputationDiscoveries.Algorithms.Grover.Solution.FindAllJohnsonRampKickMuxHi128T5
public import QuantumComputationDiscoveries.Algorithms.Grover.Solution.FindAllJohnsonRampKickMuxHi128T7

/-
# Sparse Checkpointed `kMax = 512` Table & Bounds (`FindAllJohnsonRampKickMuxHiCert128`)
-/

namespace QuantumComputation.Specs.DickeSol

@[expose] public section

/-- Part `0` of `rkmVPotHi_m128`. -/
def rkmVPotHi_m128_p0 : List ℕ := [
  0, 56807109866443, 61268963978104, 66739873855438, 67622670417223, 68207223905408,
  68645340462653, 69001302653668, 69306749694363, 69579087911114, 69828775477224, 70062678193394,
  70284638818259, 70498265407246, 70705584239871, 70908724490041, 71107472461086, 71303897608572,
  71498355863643, 71691867372193, 71885608087986, 72077643790112, 72270195775498, 72463224965940,
  72656181801862, 72850714898520, 73045300212543, 73241304451898, 73438550066318, 73637183246583,
  73837321148247, 74040616388919, 74243226073078, 84132074600246, 93874413568376, 103476567688867,
  112944419333274, 122283450667062, 97231178755747, 106327596381664, 115309589105133,
  124181369154995, 132946896509052, 141609899548412, 103624809144933, 112093113096044,
  120468864498259, 128755033095948, 136954433139267, 145069734548759, 78364200370068,
  86318786827785, 94196515575261, 101999572222811, 109730040719201, 117389909850979,
  124981079217160, 80205451097475, 87664590055108, 95060245824589, 102394012173220,
  109667417278525, 116881927446077, 124038950560693, 82367637062545, 89413691857610,
  96406163709298, 103346256757169, 110235130706152, 117073903088761, 123863651381359,
  130605414985809, 137300197086838, 143948966394503, 150552658780338, 157112178814993,
  163628401214531, 170102172201917, 176534310789708, 182925609989439, 189276837952773,
  195588739049045, 201862034883498, 208097425260142, 214295589092872, 220457185268213,
  226582853462784, 232673214918357, 238728873177166, 244750414779938, 250738409928918,
  256693413118017, 262615963732056, 268506586616931, 274365792622412, 280194079119162,
  124973010528725, 130740898644247, 136479283302272, 142188612661408, 147869323648053,
  153521842346599, 159146584372386, 164743955228317, 170314350646006, 175858156912272,
  181375751181738, 186867501776250, 192333768471796, 197774902773549, 203191248179631,
  208583140434164, 213950907770126, 219294871142519, 224615344452307, 229912634761577,
  235187042500332, 240438861665316, 245668380011237, 250875879234746, 256061635151501,
  261225917866633, 266368991938911, 271491116538890, 276592545601306, 281673527971973,
  286734307549427, 291775123421538, 104873457477681
  ]
/-- Part `1` of `rkmVPotHi_m128`. -/
def rkmVPotHi_m128_p1 : List ℕ := [
  109875044614446, 114857357740648, 119820617974398, 124765042237982, 129690843368487,
  134598230224703, 139487407790457, 144358577274522, 149211936207238, 154047678533972,
  158865994705555, 163667071765801, 168451093436228, 173218240198091, 177968689371832,
  182702615194036, 187420188891999, 192121578755994, 196806950209319, 201476465876213,
  206130285647716, 210768566745550, 215391463784096, 219999128830529, 224591711463185,
  229169358828215, 233732215694597, 238280424507556, 242814125440448, 247333456445170,
  251838553301135, 256329549662870, 260806577106282, 265269765173635, 269719241417286,
  274155131442217, 278577558947407, 282986645766077, 287382511904855, 291765275581884,
  296135053263918, 300491959702435, 304836107968794, 309167609488474, 313486574074422,
  317793109959535, 322087323828305, 326369320847657, 330639204697001, 334897077597518,
  339143040340718, 343377192316274, 347599631539169, 351810454676169, 356009757071642,
  360197632772750, 364374174554020, 368539473941328, 372693621235297, 376836705534142,
  380968814755962, 385090035660512, 389200453870454, 152600594500112, 156689659743750,
  160768172543361, 164836214176017, 168893864880763, 172941203877087, 176978309382960,
  181005258632477, 185022127893095, 189028992482485, 193025926785011, 197013004267840,
  200990297496699, 204957878151283, 208915817040328, 212864184116354, 216803048490092,
  220732478444597, 224652541449058, 228563304172316, 232464832496091, 236357191527933,
  240240445613898, 244114658350958, 247979892599153, 251836210493493, 255683673455609,
  259522342205170, 263352276771059, 267173536502331, 270986180078939, 274790265522248,
  278585850205339, 282372990863102, 286151743602134, 289922163910432, 293684306666905,
  297438226150690, 301183976050289, 304921609472529, 308651178951346, 312372736456401,
  316086333401527, 319792020653019, 323489848537760, 327179866851197, 330862124865164,
  334536671335559, 338203554509875, 341862822134590, 345514521462424, 349158699259455,
  352795401812108, 356424674934013, 360046563972741, 363661113816412, 367268368900188,
  370868373212646, 374461170302034, 378046803282421, 381625314839729, 385196747237667,
  388761142323550, 392318541534021, 143283155897958, 146826686052856
  ]
/-- Part `2` of `rkmVPotHi_m128`. -/
def rkmVPotHi_m128_p2 : List ℕ := [
  150363342233958, 153893164290450, 157416191687983, 160932463513820, 164442018481899,
  167944894937802, 171441130863646, 174930763882887, 178413831265044, 181890369930341,
  185360416454277, 188824007072112, 192281177683282, 195731963855742, 199176400830234,
  202614523524486, 206046366537342, 209471964152824, 212891350344129, 216304558777558,
  219711622816386, 223112575524663, 226507449670962, 229896277732060, 233279091896562,
  236655924068471, 240026805870696, 243391768648509, 246750843472944, 250104061144144,
  253451452194659, 256793046892685, 260128875245262, 263458967001415, 266783351655248,
  270102058448995, 273415116376019, 276722554183769, 280024400376687, 283320683219077,
  286611430737927, 289896670725689, 293176430743017, 296450738121466, 299719619966149,
  302983103158354, 306241214358123, 309493980006794, 312741426329504, 315983579337656,
  319220464831349, 322452108401775, 325678535433577, 328899771107179, 332115840401075,
  335326768094090, 338532578767610, 341733296807774, 344928946407640, 348119551569318,
  351305136106073, 354485723644400, 357661337626067, 360832001310131, 363997737774926,
  367158569920022, 370314520468158, 373465611967149, 376611866791763, 379753307145577,
  382889955062804, 386021832410095, 389148960888321, 392271362034323, 395389057222645,
  398502067667241, 401610414423159, 404714118388202, 407813200304567, 410907680760464,
  413997580191708, 417082918883299, 420163716970970, 423239994442724, 426311771140346,
  429379066760896, 432441900858182, 435500292844215, 438554261990644, 441603827430173,
  444649008157960, 447689823032996, 450726290779469, 453758429988108, 456786259117513,
  459809796495463, 462829060320213, 465844068661770, 468854839463156, 471861390541654,
  474863739590036, 477861904177781, 480855901752271, 483845749639979, 486831465047636,
  489813065063389, 492790566657939, 495763986685670, 498733341885762, 501698648883290,
  504659924190310, 507617184206931, 510570445222376, 513519723416029, 516465034858467,
  519406395512483, 522343821234097, 525277327773550, 528206930776291, 531132645783951,
  534054488235304, 536972473467217, 539886616715592, 542796933116291, 545703437706054,
  548606145423406, 212833919505318, 215729077905031, 218620483667522
  ]
/-- Part `3` of `rkmVPotHi_m128`. -/
def rkmVPotHi_m128_p3 : List ℕ := [
  221508151347309, 224392095405070, 227272330208489, 230148870033089, 233021729063060,
  235890921392073, 238756461024087, 241618361874148, 244476637769176, 247331302448744,
  250182369565850, 253029852687678, 255873765296350, 258714120789673, 261550932481873,
  264384213604327, 267213977306278, 270040236655551, 272863004639255, 275682294164480,
  278498118058985, 281310489071879, 284119419874295, 286924923060056, 289727011146333,
  292525696574299, 295320991709769, 298112908843841, 300901460193526, 303686657902371,
  306468514041076, 309247040608104, 312022249530287, 314794152663420, 317562761792855,
  320328088634082, 323090144833312, 325848941968045, 328604491547639, 331356805013868,
  334105893741478, 336851769038734, 339594442147965, 342333924246099, 345070226445195,
  347803359792968, 350533335273312, 353260163806811, 355983856251252, 358704423402129,
  361421875993140, 364136224696683, 366847480124346, 369555652827387, 372260753297218,
  374962791965876, 377661779206492, 380357725333759, 383050640604388, 385740535217565,
  388427419315402, 391111302983383, 393792196250806, 396470109091218, 399145051422850,
  401817033109047, 404486063958688, 407152153726609, 409815312114020, 412475548768914,
  415132873286477, 417787295209490, 420438824028729, 423087469183364, 425733240061347,
  428376145999802, 431016196285410, 433653400154788, 436287766794868, 438919305343268,
  441548024888664, 444173934471156, 446797043082630, 449417359667116, 452034893121147,
  454649652294108, 457261645988587, 459870882960721, 462477371920537, 465081121532292,
  467682140414809, 470280437141810, 472876020242247, 475468898200625, 478059079457328,
  480646572408941, 483231385408564, 485813526766130, 488393004748714, 490969827580844,
  493544003444806, 496115540480945, 498684446787970, 501250730423247, 503814399403097,
  506375461703087, 508933925258318, 511489797963715, 514043087674308, 516593802205516,
  519141949333425, 521687536795065, 524230572288683, 526771063474017, 529309017972562,
  531844443367840, 534377347205661, 536907736994388, 539435620205196, 541961004272327,
  544483896593349, 547004304529405, 549522235405466, 552037696510578, 554550695098110,
  192843279977351
  ]
/-- Assembled `513`-element `vPot` table (`m = 128`). -/
def rkmVPotHi_m128 : List ℕ :=
  rkmVPotHi_m128_p0 ++ (rkmVPotHi_m128_p1 ++ (rkmVPotHi_m128_p2 ++ rkmVPotHi_m128_p3))
/-- Active anchor chunk `0` (`m = 128`). -/
def rkmAncPHi_m128_p0 : List RampKickAnchor := [
  ⟨3, [1, 1, 1, 1],
    [41328097, 19592572, 1228054, 1487927],
    [3, 2, 1, 1], rkmMasksHi_m128_r3, rkmRowHi_m128_r3⟩,
  ⟨4, [1, 1, 1, 1, 1],
    [57092817, 6833491, 854452, 423277, 117534],
    [5, 1, 1, 1, 1], rkmMasksHi_m128_r4, rkmRowHi_m128_r4⟩,
  ⟨5, [1, 1, 1], [65436704, 512257, 423361], [7, 2, 2], rkmMasksHi_m128_r5, rkmRowHi_m128_r5⟩,
  ⟨6, [1, 1, 1, 1, 1, 1, 1, 1],
    [24162075, 25658153, 6554272, 4362501, 2099505, 1380187, 1607300, 1289642],
    [9, 9, 1, 1, 1, 1, 1, 1], rkmMasksHi_m128_r6, rkmRowHi_m128_r6⟩,
  ⟨7, [1, 1, 1, 1, 1, 1, 1, 1],
    [28210336, 31405817, 2192580, 1183090, 1365963, 1639208, 1571432, 113881],
    [9, 9, 1, 1, 1, 1, 1, 1], rkmMasksHi_m128_r7, rkmRowHi_m128_r7⟩,
  ⟨8, [1, 1, 1, 1, 1, 1, 1, 1],
    [28502561, 31575685, 1730448, 1182662, 1493335, 1658409, 1684045, 318950],
    [9, 9, 1, 1, 1, 1, 1, 1], rkmMasksHi_m128_r8, rkmRowHi_m128_r8⟩,
  ⟨9, [1, 1, 1, 1],
    [66268405, 1665546, 351138, 256053],
    [11, 2, 2, 2], rkmMasksHi_m128_r9, rkmRowHi_m128_r9⟩,
  ⟨10, [1, 1, 1, 1, 1, 1, 1, 1],
    [30120448, 30958948, 2259513, 1417819, 1674856, 1623509, 397120, 436162],
    [9, 9, 1, 1, 1, 1, 1, 1], rkmMasksHi_m128_r10, rkmRowHi_m128_r10⟩,
  ⟨11, [1, 1, 1, 1, 1, 1, 1, 1],
    [28904714, 32276140, 2292184, 1425989, 1693504, 1815856, 43324, 748836],
    [9, 9, 1, 1, 1, 1, 1, 1], rkmMasksHi_m128_r11, rkmRowHi_m128_r11⟩,
  ⟨12, [1, 1, 1, 1],
    [66690229, 1777994, 557002, 463911],
    [14, 2, 2, 2], rkmMasksHi_m128_r12, rkmRowHi_m128_r12⟩
  ]
/-- Active anchor chunk `1` (`m = 128`). -/
def rkmAncPHi_m128_p1 : List RampKickAnchor := [
  ⟨13, [1, 1, 1, 1],
    [66831543, 1807185, 604435, 514980],
    [15, 2, 2, 2], rkmMasksHi_m128_r13, rkmRowHi_m128_r13⟩,
  ⟨14, [1, 1, 1, 1],
    [66974544, 1847485, 655739, 534880],
    [15, 2, 2, 2], rkmMasksHi_m128_r14, rkmRowHi_m128_r14⟩,
  ⟨15, [1, 1, 1, 1, 1, 1, 1, 1],
    [30107848, 31524328, 1179493, 2599729, 1375466, 664919, 1726324, 1077013],
    [10, 11, 1, 1, 1, 1, 1, 1], rkmMasksHi_m128_r15, rkmRowHi_m128_r15⟩,
  ⟨16, [1, 1, 1, 1, 1, 1, 1, 2],
    [33294926, 29613226, 2648693, 1768795, 1608596, 577297, 980208, 36],
    [11, 11, 1, 1, 1, 1, 1, 1], rkmMasksHi_m128_r16, rkmRowHi_m128_r16⟩,
  ⟨17, [1, 1, 1, 1, 1, 1, 1, 1],
    [31068226, 30974426, 3555493, 1841895, 1390896, 325847, 901398, 661898],
    [11, 12, 1, 1, 1, 1, 1, 1], rkmMasksHi_m128_r17, rkmRowHi_m128_r17⟩,
  ⟨18, [1, 1, 1, 1, 1, 1, 1, 1],
    [31239226, 30932026, 3561993, 1865895, 1486696, 345847, 800598, 710298],
    [11, 12, 1, 1, 1, 1, 1, 1], rkmMasksHi_m128_r18, rkmRowHi_m128_r18⟩,
  ⟨19, [1, 1, 1, 1, 1, 1, 1, 2],
    [29817226, 32529026, 3437193, 1975395, 1846596, 760897, 792428, 36],
    [12, 13, 1, 1, 1, 1, 1, 1], rkmMasksHi_m128_r19, rkmRowHi_m128_r19⟩,
  ⟨20, [1, 1, 1, 1, 1, 1, 1, 1],
    [30194626, 32258226, 3277641, 2020145, 1012946, 1207247, 972598, 430648],
    [13, 13, 1, 1, 1, 1, 1, 1], rkmMasksHi_m128_r20, rkmRowHi_m128_r20⟩,
  ⟨21, [1, 1, 1, 1, 1, 1, 1, 1],
    [30164176, 32324776, 2483743, 3048746, 1686746, 315498, 866498, 695392],
    [13, 14, 1, 1, 1, 1, 1, 1], rkmMasksHi_m128_r21, rkmRowHi_m128_r21⟩,
  ⟨22, [1, 1, 1, 1, 1, 1, 1, 1],
    [31811975, 30815775, 2555542, 2992145, 1840296, 109397, 825898, 845348],
    [14, 14, 1, 1, 1, 1, 1, 1], rkmMasksHi_m128_r22, rkmRowHi_m128_r22⟩
  ]
/-- Active anchor chunk `2` (`m = 128`). -/
def rkmAncPHi_m128_p2 : List RampKickAnchor := [
  ⟨23, [1, 1, 1, 1, 1, 1, 1, 1],
    [30148926, 32608926, 2623694, 2883045, 1280025, 839547, 921448, 699098],
    [14, 15, 1, 1, 1, 1, 1, 1], rkmMasksHi_m128_r23, rkmRowHi_m128_r23⟩,
  ⟨24, [1, 1, 1, 1, 1, 1, 1, 1],
    [31793448, 33539048, 2087313, 1067719, 1182806, 822059, 873578, 847262],
    [15, 15, 1, 1, 1, 1, 1, 1], rkmMasksHi_m128_r24, rkmRowHi_m128_r24⟩,
  ⟨25, [1, 1, 1, 1, 1, 1, 1, 1],
    [32347098, 33127798, 2061663, 1029369, 1237806, 963759, 999328, 653662],
    [15, 15, 1, 1, 1, 1, 1, 1], rkmMasksHi_m128_r25, rkmRowHi_m128_r25⟩,
  ⟨26, [1, 1, 1, 1, 1, 1, 1, 1],
    [32589598, 33032498, 2081163, 1101869, 1489906, 631559, 975828, 724062],
    [15, 15, 1, 1, 1, 1, 1, 1], rkmMasksHi_m128_r26, rkmRowHi_m128_r26⟩,
  ⟨27, [1, 1, 1, 1, 1, 1, 1, 1],
    [32839127, 32929931, 2099472, 1102039, 1502006, 617359, 978828, 765462],
    [15, 15, 1, 1, 1, 1, 1, 1], rkmMasksHi_m128_r27, rkmRowHi_m128_r27⟩,
  ⟨28, [1, 1, 1, 1, 1, 1, 1, 1],
    [33088637, 32831560, 2104132, 1109550, 1530707, 591880, 978479, 806862],
    [15, 15, 1, 1, 1, 1, 1, 1], rkmMasksHi_m128_r28, rkmRowHi_m128_r28⟩,
  ⟨29, [1, 1, 1, 1, 1, 1, 1, 1],
    [33037787, 33032610, 2106840, 1123360, 1557207, 573780, 984529, 833762],
    [15, 15, 1, 1, 1, 1, 1, 1], rkmMasksHi_m128_r29, rkmRowHi_m128_r29⟩,
  ⟨30, [1, 1, 1, 1, 1, 1, 1, 1],
    [32987287, 33235711, 2109041, 1135562, 1573207, 572880, 996307, 848662],
    [15, 15, 1, 1, 1, 1, 1, 1], rkmMasksHi_m128_r30, rkmRowHi_m128_r30⟩,
  ⟨31, [1, 1, 1, 1, 1, 1, 1, 1],
    [32623568, 32596839, 2198289, 580635, 1760660, 1841292, 441116, 1626961],
    [15, 15, 1, 1, 1, 1, 1, 1], rkmMasksHi_m128_r31, rkmRowHi_m128_r31⟩,
  ⟨32, [1, 1, 1, 1, 1, 1, 1, 1],
    [31525606, 31445228, 3450714, 1683516, 1834285, 2050007, 243245, 1647564],
    [17, 17, 2, 2, 1, 1, 1, 1], rkmMasksHi_m128_r32, rkmRowHi_m128_r32⟩
  ]
/-- Active anchor chunk `3` (`m = 128`). -/
def rkmAncPHi_m128_p3 : List RampKickAnchor := [
  ⟨38, [1, 1, 1, 1, 1, 1, 1, 1],
    [3727215, 6152779, 4663358, 1165207, 2211204, 1227195, 623020, 1998915],
    [3, 4, 3, 1, 2, 1, 1, 2], rkmMasksHiHiB_m128_r38, rkmRowHiHiB_m128_r38⟩,
  ⟨44, [1, 1, 1, 1, 1, 1, 1, 1],
    [7517247, 3730290, 9725635, 1000, 1325175, 2188018, 923660, 3381375],
    [5, 3, 7, 1, 1, 2, 1, 3], rkmMasksHiHiB_m128_r44, rkmRowHiHiB_m128_r44⟩,
  ⟨50, [1, 1, 1, 1, 1, 1, 1, 1],
    [9431622, 25909382, 17856452, 8804058, 4819570, 4452821, 4548241, 2209112],
    [7, 19, 13, 7, 4, 4, 4, 2], rkmMasksHiHiB_m128_r50, rkmRowHiHiB_m128_r50⟩,
  ⟨57, [1, 1, 1, 1, 1, 1, 1, 1],
    [19717878, 24789701, 14954997, 4571130, 5576698, 5204442, 2975129, 2071756],
    [16, 20, 12, 4, 5, 5, 3, 2], rkmMasksHiHiB_m128_r57, rkmRowHiHiB_m128_r57⟩,
  ⟨64, [1, 1, 1, 1, 1, 1, 1, 1],
    [20806197, 17724820, 16445970, 9400784, 6696938, 3478755, 4843920, 2552589],
    [18, 16, 15, 9, 6, 4, 5, 3], rkmMasksHiHiB_m128_r64, rkmRowHiHiB_m128_r64⟩,
  ⟨96, [1, 1, 1, 1, 1, 1, 1, 1],
    [14578303, 20720775, 13335033, 632279, 811554, 417711, 436472, 172022],
    [18, 25, 17, 1, 1, 1, 1, 1], rkmMasksHiHiB_m128_r96, rkmRowHiHiB_m128_r96⟩,
  ⟨128, [1, 1, 2, 2, 2, 2, 2, 2],
    [19324585, 23012918, 12552501, 12552501, 2010242, 1942135, 692434, 877181],
    [30, 35, 31, 31, 5, 5, 2, 3], rkmMasksHiHiB_m128_r128, rkmRowHiHiB_m128_r128⟩,
  ⟨192, [1, 1, 2, 2, 2, 2, 2, 2],
    [12311628, 18861414, 9846983, 10218327, 1278670, 1278585, 417309, 724230],
    [25, 38, 34, 35, 5, 5, 2, 3], rkmMasksHiHiB_m128_r192, rkmRowHiHiB_m128_r192⟩,
  ⟨256, [1, 2, 3, 3, 3, 3, 3, 3],
    [16430684, 10460158, 29500000, 2230754, 1002839, 1095694, 650947, 327022],
    [40, 45, 167, 13, 6, 7, 4, 2], rkmMasksHiHiB_m128_r256, rkmRowHiHiB_m128_r256⟩,
  ⟨384, [1, 2, 3, 3, 3, 3, 3, 3],
    [15515711, 6940628, 30108311, 2464979, 1292070, 1142242, 521425, 459510],
    [49, 40, 234, 20, 11, 9, 5, 4], rkmMasksHiHiB_m128_r384, rkmRowHiHiB_m128_r384⟩
  ]
/-- Active anchor chunk `4` (`m = 128`). -/
def rkmAncPHi_m128_p4 : List RampKickAnchor := [
  ⟨512, [1, 2, 3, 5, 7, 7, 7, 7],
    [13240546, 8842920, 5680876, 5000000, 13800000, 1526245, 689986, 541950],
    [49, 61, 55, 71, 244, 27, 13, 10], rkmMasksHiHiB_m128_r512, rkmRowHiHiB_m128_r512⟩
  ]
/-- Sorted active multi-segment anchors (`m = 128, kMax = 512`). -/
def rkmAnchorsHi_m128 : List RampKickAnchor :=
  rkmAncPHi_m128_p0 ++ (rkmAncPHi_m128_p1 ++ (rkmAncPHi_m128_p2 ++ (rkmAncPHi_m128_p3 ++
    rkmAncPHi_m128_p4)))
private theorem rkm_anc_app_hi_128 {m0 lMax : ℕ} :
    ∀ {xs ys : List RampKickAnchor},
      RampKickAnchorsSound m0 lMax xs → RampKickAnchorsSound m0 lMax ys →
      RampKickAnchorsSound m0 lMax (xs ++ ys)
  | [], _, _, hy => hy
  | _ :: _, _, ⟨hx0, hxs⟩, hy =>
      ⟨hx0, rkm_anc_app_hi_128 hxs hy⟩
private theorem rkmAncSndPHi_m128_p0 : RampKickAnchorsSound 128 64 rkmAncPHi_m128_p0 :=
  ⟨rkmTrajHi_m128_r3, ⟨rkmTrajHi_m128_r4, ⟨rkmTrajHi_m128_r5, ⟨rkmTrajHi_m128_r6,
    ⟨rkmTrajHi_m128_r7, ⟨rkmTrajHi_m128_r8, ⟨rkmTrajHi_m128_r9, ⟨rkmTrajHi_m128_r10,
    ⟨rkmTrajHi_m128_r11, ⟨rkmTrajHi_m128_r12, trivial⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
private theorem rkmAncSndPHi_m128_p1 : RampKickAnchorsSound 128 64 rkmAncPHi_m128_p1 :=
  ⟨rkmTrajHi_m128_r13, ⟨rkmTrajHi_m128_r14, ⟨rkmTrajHi_m128_r15, ⟨rkmTrajHi_m128_r16,
    ⟨rkmTrajHi_m128_r17, ⟨rkmTrajHi_m128_r18, ⟨rkmTrajHi_m128_r19, ⟨rkmTrajHi_m128_r20,
    ⟨rkmTrajHi_m128_r21, ⟨rkmTrajHi_m128_r22, trivial⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
private theorem rkmAncSndPHi_m128_p2 : RampKickAnchorsSound 128 64 rkmAncPHi_m128_p2 :=
  ⟨rkmTrajHi_m128_r23, ⟨rkmTrajHi_m128_r24, ⟨rkmTrajHi_m128_r25, ⟨rkmTrajHi_m128_r26,
    ⟨rkmTrajHi_m128_r27, ⟨rkmTrajHi_m128_r28, ⟨rkmTrajHi_m128_r29, ⟨rkmTrajHi_m128_r30,
    ⟨rkmTrajHi_m128_r31, ⟨rkmTrajHi_m128_r32, trivial⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
private theorem rkmAncSndPHi_m128_p3 : RampKickAnchorsSound 128 64 rkmAncPHi_m128_p3 :=
  ⟨rkmTrajHiHiB_m128_r38, ⟨rkmTrajHiHiB_m128_r44, ⟨rkmTrajHiHiB_m128_r50,
    ⟨rkmTrajHiHiB_m128_r57, ⟨rkmTrajHiHiB_m128_r64, ⟨rkmTrajHiHiB_m128_r96,
    ⟨rkmTrajHiHiB_m128_r128, ⟨rkmTrajHiHiB_m128_r192, ⟨rkmTrajHiHiB_m128_r256,
    ⟨rkmTrajHiHiB_m128_r384, trivial⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
private theorem rkmAncSndPHi_m128_p4 : RampKickAnchorsSound 128 64 rkmAncPHi_m128_p4 :=
  ⟨rkmTrajHiHiB_m128_r512, trivial⟩
/-- Anchor trajectory soundness bundle (`m = 128, kMax = 512`). -/
theorem rkmAnchorsSoundHi_m128 :
    RampKickAnchorsSound 128 64 rkmAnchorsHi_m128 :=
  rkm_anc_app_hi_128 rkmAncSndPHi_m128_p0 (rkm_anc_app_hi_128 rkmAncSndPHi_m128_p1
    (rkm_anc_app_hi_128 rkmAncSndPHi_m128_p2 (rkm_anc_app_hi_128 rkmAncSndPHi_m128_p3
    rkmAncSndPHi_m128_p4)))
private theorem rkmTableAndBndHi_m128 : rkmAllTrueF [
  rkmCheckTable 128 512 64 true rkmVPotHi_m128 rkmAnchorsHi_m128,
  rkmCheckAnchorsLMax 2 1 rkmAnchorsHi_m128,
  rkmCheckAnchorsLMax 2 2 rkmAnchorsHi_m128,
  checkAltBound12 128 2 (rkmVPotHi_m128.getD 2 0) 517005249363 1000000000000,
  rkmCheckAnchorsLMax 4 1 rkmAnchorsHi_m128,
  rkmCheckAnchorsLMax 4 2 rkmAnchorsHi_m128,
  checkAltBound12 128 4 (rkmVPotHi_m128.getD 4 0) 17491896601 50000000000,
  rkmCheckAnchorsLMax 8 1 rkmAnchorsHi_m128,
  rkmCheckAnchorsLMax 8 2 rkmAnchorsHi_m128,
  checkAltBound12 128 8 (rkmVPotHi_m128.getD 8 0) 228384397809 1000000000000,
  rkmCheckAnchorsLMax 16 2 rkmAnchorsHi_m128,
  rkmCheckAnchorsLMax 16 2 rkmAnchorsHi_m128,
  checkAltBound12 128 16 (rkmVPotHi_m128.getD 16 0) 19213466223 125000000000,
  rkmCheckAnchorsLMax 32 2 rkmAnchorsHi_m128,
  rkmCheckAnchorsLMax 32 2 rkmAnchorsHi_m128,
  checkAltBound12 128 32 (rkmVPotHi_m128.getD 32 0) 26894253763 250000000000,
  rkmCheckAnchorsLMax 64 2 rkmAnchorsHi_m128,
  rkmCheckAnchorsLMax 64 2 rkmAnchorsHi_m128,
  checkAltBound12 128 64 (rkmVPotHi_m128.getD 64 0) 20314094501 250000000000,
  rkmCheckAnchorsLMax 128 2 rkmAnchorsHi_m128,
  rkmCheckAnchorsLMax 128 2 rkmAnchorsHi_m128,
  checkAltBound12 128 128 (rkmVPotHi_m128.getD 128 0) 71222117181 1000000000000,
  rkmCheckAnchorsLMax 256 3 rkmAnchorsHi_m128,
  rkmCheckAnchorsLMax 256 3 rkmAnchorsHi_m128,
  checkAltBound12 128 256 (rkmVPotHi_m128.getD 256 0) 67515303789 1000000000000,
  rkmCheckAnchorsLMax 512 7 rkmAnchorsHi_m128,
  rkmCheckAnchorsLMax 512 7 rkmAnchorsHi_m128,
  checkAltBound12 128 512 (rkmVPotHi_m128.getD 512 0) 12679764911 200000000000
  ] = true := by decide +kernel
private theorem rkmHd {b : Bool} {bs : List Bool} (h : rkmAllTrueF (b :: bs) = true) :
    b = true := (rkmAllTrueF_cons h).1
private theorem t1 {b : Bool} {bs : List Bool} (h : rkmAllTrueF (b :: bs) = true) :
    rkmAllTrueF bs = true := (rkmAllTrueF_cons h).2
private theorem t2 {b0 b1 : Bool} {bs : List Bool}
    (h : rkmAllTrueF (b0 :: b1 :: bs) = true) : rkmAllTrueF bs = true := t1 (t1 h)
private theorem t4 {b0 b1 b2 b3 : Bool} {bs : List Bool}
    (h : rkmAllTrueF (b0 :: b1 :: b2 :: b3 :: bs) = true) : rkmAllTrueF bs = true :=
  t2 (t2 h)
private theorem t8 {b0 b1 b2 b3 b4 b5 b6 b7 : Bool} {bs : List Bool}
    (h : rkmAllTrueF (b0 :: b1 :: b2 :: b3 :: b4 :: b5 :: b6 :: b7 :: bs) = true) :
    rkmAllTrueF bs = true := t4 (t4 h)
/-- Kernel Bellman table verification (`m = 128, kMax = 512`). -/
theorem rkmTableOkHi_m128 :
    rkmCheckTable 128 512 64 true rkmVPotHi_m128 rkmAnchorsHi_m128 = true :=
  rkmHd rkmTableAndBndHi_m128
/-- Unpacked `RampKickTableValid` bundle (`m = 128, kMax = 512`). -/
theorem rkmValidHi_m128 :
    RampKickTableValid 128 512 64 true rkmVPotHi_m128 rkmAnchorsHi_m128 :=
  rkmCheckTable_sound rkmTableOkHi_m128 rkmAnchorsSoundHi_m128
/-- Cell `lMax = 1` bound for `(128, 2)`. -/
theorem rkmCellLMaxHi_m128_k2 :
    rkmCheckAnchorsLMax 2 1 rkmAnchorsHi_m128 = true :=
  rkmHd (t1 rkmTableAndBndHi_m128)
/-- Cold-`r2` `lMax = 2` (`>= 2`) bound for `(128, 2)`. -/
theorem rkmCellLMax2Hi_m128_k2 :
    rkmCheckAnchorsLMax 2 2 rkmAnchorsHi_m128 = true :=
  rkmHd (t2 rkmTableAndBndHi_m128)
/-- Relative-cost certificate `517005249363 / 1000000000000` for `(128, 2)`. -/
theorem rkmBoundHi_m128_k2 :
    checkAltBound12 128 2 (rkmVPotHi_m128.getD 2 0) 517005249363 1000000000000 = true :=
  rkmHd (t1 (t2 rkmTableAndBndHi_m128))
/-- Cell `lMax = 1` bound for `(128, 4)`. -/
theorem rkmCellLMaxHi_m128_k4 :
    rkmCheckAnchorsLMax 4 1 rkmAnchorsHi_m128 = true :=
  rkmHd (t4 rkmTableAndBndHi_m128)
/-- Cold-`r2` `lMax = 2` (`>= 2`) bound for `(128, 4)`. -/
theorem rkmCellLMax2Hi_m128_k4 :
    rkmCheckAnchorsLMax 4 2 rkmAnchorsHi_m128 = true :=
  rkmHd (t1 (t4 rkmTableAndBndHi_m128))
/-- Relative-cost certificate `17491896601 / 50000000000` for `(128, 4)`. -/
theorem rkmBoundHi_m128_k4 :
    checkAltBound12 128 4 (rkmVPotHi_m128.getD 4 0) 17491896601 50000000000 = true :=
  rkmHd (t2 (t4 rkmTableAndBndHi_m128))
/-- Cell `lMax = 1` bound for `(128, 8)`. -/
theorem rkmCellLMaxHi_m128_k8 :
    rkmCheckAnchorsLMax 8 1 rkmAnchorsHi_m128 = true :=
  rkmHd (t1 (t2 (t4 rkmTableAndBndHi_m128)))
/-- Cold-`r2` `lMax = 2` (`>= 2`) bound for `(128, 8)`. -/
theorem rkmCellLMax2Hi_m128_k8 :
    rkmCheckAnchorsLMax 8 2 rkmAnchorsHi_m128 = true :=
  rkmHd (t8 rkmTableAndBndHi_m128)
/-- Relative-cost certificate `228384397809 / 1000000000000` for `(128, 8)`. -/
theorem rkmBoundHi_m128_k8 :
    checkAltBound12 128 8 (rkmVPotHi_m128.getD 8 0) 228384397809 1000000000000 = true :=
  rkmHd (t1 (t8 rkmTableAndBndHi_m128))
/-- Cell `lMax = 2` bound for `(128, 16)`. -/
theorem rkmCellLMaxHi_m128_k16 :
    rkmCheckAnchorsLMax 16 2 rkmAnchorsHi_m128 = true :=
  rkmHd (t2 (t8 rkmTableAndBndHi_m128))
/-- Cold-`r2` `lMax = 2` (`>= 2`) bound for `(128, 16)`. -/
theorem rkmCellLMax2Hi_m128_k16 :
    rkmCheckAnchorsLMax 16 2 rkmAnchorsHi_m128 = true :=
  rkmHd (t1 (t2 (t8 rkmTableAndBndHi_m128)))
/-- Relative-cost certificate `19213466223 / 125000000000` for `(128, 16)`. -/
theorem rkmBoundHi_m128_k16 :
    checkAltBound12 128 16 (rkmVPotHi_m128.getD 16 0) 19213466223 125000000000 = true :=
  rkmHd (t4 (t8 rkmTableAndBndHi_m128))
/-- Cell `lMax = 2` bound for `(128, 32)`. -/
theorem rkmCellLMaxHi_m128_k32 :
    rkmCheckAnchorsLMax 32 2 rkmAnchorsHi_m128 = true :=
  rkmHd (t1 (t4 (t8 rkmTableAndBndHi_m128)))
/-- Cold-`r2` `lMax = 2` (`>= 2`) bound for `(128, 32)`. -/
theorem rkmCellLMax2Hi_m128_k32 :
    rkmCheckAnchorsLMax 32 2 rkmAnchorsHi_m128 = true :=
  rkmHd (t2 (t4 (t8 rkmTableAndBndHi_m128)))
/-- Relative-cost certificate `26894253763 / 250000000000` for `(128, 32)`. -/
theorem rkmBoundHi_m128_k32 :
    checkAltBound12 128 32 (rkmVPotHi_m128.getD 32 0) 26894253763 250000000000 = true :=
  rkmHd (t1 (t2 (t4 (t8 rkmTableAndBndHi_m128))))
/-- Cell `lMax = 2` bound for `(128, 64)`. -/
theorem rkmCellLMaxHi_m128_k64 :
    rkmCheckAnchorsLMax 64 2 rkmAnchorsHi_m128 = true :=
  rkmHd (t8 (t8 rkmTableAndBndHi_m128))
/-- Cold-`r2` `lMax = 2` (`>= 2`) bound for `(128, 64)`. -/
theorem rkmCellLMax2Hi_m128_k64 :
    rkmCheckAnchorsLMax 64 2 rkmAnchorsHi_m128 = true :=
  rkmHd (t1 (t8 (t8 rkmTableAndBndHi_m128)))
/-- Relative-cost certificate `20314094501 / 250000000000` for `(128, 64)`. -/
theorem rkmBoundHi_m128_k64 :
    checkAltBound12 128 64 (rkmVPotHi_m128.getD 64 0) 20314094501 250000000000 = true :=
  rkmHd (t2 (t8 (t8 rkmTableAndBndHi_m128)))
/-- Cell `lMax = 2` bound for `(128, 128)`. -/
theorem rkmCellLMaxHi_m128_k128 :
    rkmCheckAnchorsLMax 128 2 rkmAnchorsHi_m128 = true :=
  rkmHd (t1 (t2 (t8 (t8 rkmTableAndBndHi_m128))))
/-- Cold-`r2` `lMax = 2` (`>= 2`) bound for `(128, 128)`. -/
theorem rkmCellLMax2Hi_m128_k128 :
    rkmCheckAnchorsLMax 128 2 rkmAnchorsHi_m128 = true :=
  rkmHd (t4 (t8 (t8 rkmTableAndBndHi_m128)))
/-- Relative-cost certificate `71222117181 / 1000000000000` for `(128, 128)`. -/
theorem rkmBoundHi_m128_k128 :
    checkAltBound12 128 128 (rkmVPotHi_m128.getD 128 0) 71222117181 1000000000000 = true :=
  rkmHd (t1 (t4 (t8 (t8 rkmTableAndBndHi_m128))))
/-- Cell `lMax = 3` bound for `(128, 256)`. -/
theorem rkmCellLMaxHi_m128_k256 :
    rkmCheckAnchorsLMax 256 3 rkmAnchorsHi_m128 = true :=
  rkmHd (t2 (t4 (t8 (t8 rkmTableAndBndHi_m128))))
/-- Cold-`r2` `lMax = 3` (`>= 2`) bound for `(128, 256)`. -/
theorem rkmCellLMax2Hi_m128_k256 :
    rkmCheckAnchorsLMax 256 3 rkmAnchorsHi_m128 = true :=
  rkmHd (t1 (t2 (t4 (t8 (t8 rkmTableAndBndHi_m128)))))
/-- Relative-cost certificate `67515303789 / 1000000000000` for `(128, 256)`. -/
theorem rkmBoundHi_m128_k256 :
    checkAltBound12 128 256 (rkmVPotHi_m128.getD 256 0) 67515303789 1000000000000 = true :=
  rkmHd (t8 (t8 (t8 rkmTableAndBndHi_m128)))
/-- Cell `lMax = 7` bound for `(128, 512)`. -/
theorem rkmCellLMaxHi_m128_k512 :
    rkmCheckAnchorsLMax 512 7 rkmAnchorsHi_m128 = true :=
  rkmHd (t1 (t8 (t8 (t8 rkmTableAndBndHi_m128))))
/-- Cold-`r2` `lMax = 7` (`>= 2`) bound for `(128, 512)`. -/
theorem rkmCellLMax2Hi_m128_k512 :
    rkmCheckAnchorsLMax 512 7 rkmAnchorsHi_m128 = true :=
  rkmHd (t2 (t8 (t8 (t8 rkmTableAndBndHi_m128))))
/-- Relative-cost certificate `12679764911 / 200000000000` for `(128, 512)`. -/
theorem rkmBoundHi_m128_k512 :
    checkAltBound12 128 512 (rkmVPotHi_m128.getD 512 0) 12679764911 200000000000 = true :=
  rkmHd (t1 (t2 (t8 (t8 (t8 rkmTableAndBndHi_m128)))))

/-- Terminal `1`-lane table closure for `FindAllJohnsonRampKickMuxHiCert128`. -/
theorem laneClosure_FindAllJohnsonRampKickMuxHiCert128 :
    rkmTrajHiHiB_m128_r512 = rkmTrajHiHiB_m128_r512 :=
  (And.intro (Eq.refl laneWitness_FindAllJohnsonRampKickMuxHi128T7) rfl).right

end
end QuantumComputation.Specs.DickeSol
