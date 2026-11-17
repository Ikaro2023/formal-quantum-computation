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
public import QuantumComputationDiscoveries.Algorithms.Grover.Solution.FindAllJohnsonRampKickMuxHi256T0
public import QuantumComputationDiscoveries.Algorithms.Grover.Solution.FindAllJohnsonRampKickMuxHi256T1
public import QuantumComputationDiscoveries.Algorithms.Grover.Solution.FindAllJohnsonRampKickMuxHi256T2
public import QuantumComputationDiscoveries.Algorithms.Grover.Solution.FindAllJohnsonRampKickMuxHi256T3
public import QuantumComputationDiscoveries.Algorithms.Grover.Solution.FindAllJohnsonRampKickMuxHi256T4
public import QuantumComputationDiscoveries.Algorithms.Grover.Solution.FindAllJohnsonRampKickMuxHi256T5
public import QuantumComputationDiscoveries.Algorithms.Grover.Solution.FindAllJohnsonRampKickMuxHi256T6
public import QuantumComputationDiscoveries.Algorithms.Grover.Solution.FindAllJohnsonRampKickMuxHi256T7
public import QuantumComputationDiscoveries.Algorithms.Grover.Solution.FindAllJohnsonRampKickMuxHi256T8

/-
# Sparse Checkpointed `kMax = 512` Table & Bounds (`FindAllJohnsonRampKickMuxHiCert256`)
-/

namespace QuantumComputation.Specs.DickeSol

@[expose] public section

/-- Part `0` of `rkmVPotHi_m256`. -/
def rkmVPotHi_m256_p0 : List ℕ := [
  0, 40168692606172, 43079728286640, 47102760966021, 47677275119096, 48039244125377,
  48296234584485, 48493816538189, 48654598159324, 48791068167903, 48910687378667, 49018187390929,
  49116552750478, 49207895006448, 49293991252798, 49375855553199, 49454347713411, 49530090183401,
  49603595977378, 49675263245302, 49745405346018, 49814289647378, 49882109467783, 49949070463880,
  50015236388635, 50080493378334, 50145463905993, 50210048103107, 50274317276743, 50338319120361,
  50403001219179, 50465958912452, 50530420057142, 57522891908830, 64411765857813, 71201514150411,
  77896296251440, 84499988637275, 91016211036813, 97448349624604, 103799577587938, 110072873422391,
  116271037255121, 122396705449692, 128452363708501, 134440358857481, 140362909471520,
  146222115477001, 51569050826879, 57307435484904, 62988146471549, 68612888497336, 74183283915025,
  79700878184491, 85167144880037, 90583490286119, 95951257622081, 101271730931869, 106546138670624,
  111775657016545, 116961412933300, 122104487005578, 127205916067994, 132266695645448,
  52642259669210, 57624572795412, 62568997058996, 67476383915212, 72347553399277, 77183295726011,
  81984372786257, 86751519548120, 91485445370324, 96186835234319, 100856350901213, 105494631999047,
  110102297045480, 114679944410510, 119228153223469, 123747484228191, 128238480589926,
  132701668657279, 137137558682210, 141546645500880, 145929409177909, 150286315616426,
  154617817136106, 158924353021219, 163206350040571, 167464222941088, 171698374916644,
  175909198053644, 180097073754752, 184262373142060, 188405457440905, 192526678345455,
  84663509490832, 88742022290443, 92799672995189, 96836778501062, 100853647761680, 104850582064206,
  108827875293065, 112785814182110, 116724678555848, 120644741560309, 124546269884084,
  128429523970049, 132294758218244, 136142221180360, 139972155746249, 143784799322857,
  147580384005948, 151359136744980, 155121279501453, 158867029401052, 162596598879869,
  166310195824995, 170008023709736, 173690281723703, 177357164898019, 181008864225853,
  184645566778506, 188267455817234, 191874710901010, 195467507990398, 199046019547706,
  202610414633589, 58243632224725
  ]
/-- Part `1` of `rkmVPotHi_m256`. -/
def rkmVPotHi_m256_p1 : List ℕ := [
  61780288405827, 65303315803360, 68812870771439, 72309106697283, 75792174079440, 79262220603376,
  82719391214546, 86163828189038, 89595671201894, 93015057393199, 96422121432027, 99816995578326,
  103199809742828, 106570691545053, 109929766369488, 113277157420003, 116612985772580,
  119937370426413, 123250428353437, 126552274546355, 129843022065205, 133122782082533,
  136391663927216, 139649775126985, 142897221449695, 146134106943388, 149360533975190,
  152576603269086, 155782413942606, 158978063542472, 162163648079227, 165339262060894,
  168504998525689, 171660949073825, 174807203898439, 177943851815666, 181070980293892,
  184188675482214, 187297022238132, 190396104154497, 193486003585741, 196566801673412,
  199638578371034, 202701412468320, 205755381614749, 208800562342536, 211837030089009,
  214864859218414, 217884123043164, 220894893844550, 223897242892932, 226891240467422,
  229876955875079, 232854457469629, 235823812669721, 238785087976741, 241738348992186,
  244683660434624, 247621086156238, 250550689158979, 253472531610332, 256386674858707,
  259293179448470, 95287113917501, 98178519679992, 101062463737753, 103939003562353,
  106808195891366, 109670096741427, 112524761420995, 115372244542823, 118212600036146,
  121045881158600, 123872140507873, 126691430033098, 129503801045992, 132309304231753,
  135107989659719, 137899906793791, 140685104502636, 143463631069664, 146235534202797,
  149000861044024, 151759658178757, 154511971644986, 157257846942242, 159997329040376,
  162730462388149, 165457290921648, 168177858072525, 170892206776068, 173600379479109,
  176302418147767, 178998364275034, 181688258888211, 184372142556192, 187050055396604,
  189722037082801, 192388126850722, 195048363505616, 197702785428629, 200351430583264,
  202994336521719, 205631540391097, 208263078939497, 210888988521989, 213509305106475,
  216124064279436, 218733301251570, 221337050863325, 223935347590326, 226528225548704,
  229115718500317, 231697859857883, 234274682690013, 236846219726152, 239412503361429,
  241973565661419, 244529438366816, 247080152898024, 249625740359664, 252166231544998,
  254701656940276, 257232046729003, 259757430796134, 262277838732190, 264793299837302,
  73861235360204, 76366889562072
  ]
/-- Part `2` of `rkmVPotHi_m256`. -/
def rkmVPotHi_m256_p2 : List ℕ := [
  78867683130455, 81363644242983, 83854800806084, 86341180458629, 88822810575504, 91299718271132,
  93771930402924, 96239473574682, 98702374139935, 101160658205224, 103614351633332,
  106063480046457, 108508068829334, 110948143132305, 113383727874338, 115814847745995,
  118241527212353, 120663790515877, 123081661679244, 125495164508125, 127904322593917,
  130309159316435, 132709697846558, 135105961148836, 137497971984050, 139885752911736,
  142269326292668, 144648714291300, 147023938878171, 149395021832271, 151761984743373,
  154124849014325, 156483635863307, 158838366326056, 161189061258054, 163535741336683,
  165878427063346, 168217138765559, 170551896599006, 172882720549569, 175209630435321,
  177532645908493, 179851786457410, 182167071408401, 184478519927674, 186786151023171,
  189089983546388, 191390036194174, 193686327510502, 195978875888211, 198267699570726,
  200552816653752, 202834245086943, 205112002675547, 207386107082027, 209656575827658,
  211923426294104, 214186675724970, 216446341227331, 218702439773242, 220954988201225,
  223204003217734, 225449501398602, 227691499190466, 229930012912172, 232165058756162,
  234396652789839, 236624810956915, 238849549078741, 241070882855616, 243288827868082,
  245503399578196, 247714613330791, 249922484354714, 252127027764049, 254328258559328,
  256526191628717, 258720841749195, 260912223587710, 263100351702324, 265285240543341,
  267466904454422, 269645357673681, 271820614334770, 273992688467950, 276161594001145,
  278327344760985, 280489954473835, 282649436766809, 284805805168772, 286959073111329,
  289109253929800, 291256360864185, 293400407060116, 295541405569792, 297679369352912,
  299814311277584, 301946244121233, 304075180571492, 306201133227082, 308324114598682,
  310444137109790, 312561213097568, 314675354813683, 316786574425131, 318894884015056,
  321000295583556, 323102821048481, 325202472246218, 327299260932470, 329393198783024,
  331484297394509, 333572568285144, 335658022895482, 337740672589136, 339820528653506,
  341897602300491, 343971904667193, 346043446816616, 348112239738352, 350178294349262,
  352241621494150, 354302231946425, 356360136408758, 358415345513729, 360467869824471,
  115500535775980, 117547721913026, 119592254534845
  ]
/-- Part `3` of `rkmVPotHi_m256`. -/
def rkmVPotHi_m256_p3 : List ℕ := [
  121634143933036, 123673400332842, 125710033893749, 127744054710077, 129775472811562,
  131804298163935, 133830540669491, 135854210167653, 137875316435530, 139893869188467,
  141909878080591, 143923352705350, 145934302596044, 147942737226353, 149948666010857,
  151952098305552, 153953043408357, 155951510559620, 157947508942614, 159941047684029,
  161932135854460, 163920782468890, 165906996487162, 167890786814454, 169872162301743,
  171851131746266, 173827703891975, 175801887429988, 177773690999037, 179743123185906,
  181710192525870, 183674907503123, 185637276551208, 187597308053439, 189555010343317,
  191510391704946, 193463460373440, 195414224535328, 197362692328954, 199308871844875,
  201252771126251, 203194398169234, 205133760923350, 207070867291880, 209005725132237,
  210938342256335, 212868726430959, 214796885378129, 216722826775460, 218646558256518,
  220568087411175, 222487421785956, 224404568884385, 226319536167330, 228232331053339,
  230142960918975, 232051433099151, 233957754887455, 235861933536477, 237763976258132,
  239663890223975, 241561682565521, 243457360374553, 245350930703435, 247242400565415,
  249131776934931, 251019066747908, 252904276902057, 254787414257169, 256668485635406,
  258547497821588, 260424457563481, 262299371572077, 264172246521877, 266043089051165,
  267911905762285, 269778703221912, 271643487961321, 273506266476653, 275367045229181,
  277225830645569, 279082629118132, 280937447005094, 282790290630840, 284641166286168,
  286490080228539, 288337038682322, 290182047839041, 292025113857615, 293866242864599,
  295705440954421, 297542714189619, 299378068601071, 301211510188229, 303043044919346,
  304872678731704, 306700417531837, 308526267195754, 310350233569161, 312172322467677,
  313992539677051, 315810890953378, 317627382023308, 319442018584261, 321254806304631,
  323065750823995, 324874857753318, 326682132675154, 328487581143848, 330291208685736,
  332093020799342, 333893022955571, 335691220597907, 337487619142601, 339282223978865,
  341075040469059, 342866073948876, 344655329727530, 346442813087940, 348228529286909,
  350012483555307, 351794681098249, 353575127095271, 355353826700507, 357130785042863,
  100943069497630
  ]
/-- Assembled `513`-element `vPot` table (`m = 256`). -/
def rkmVPotHi_m256 : List ℕ :=
  rkmVPotHi_m256_p0 ++ (rkmVPotHi_m256_p1 ++ (rkmVPotHi_m256_p2 ++ rkmVPotHi_m256_p3))
/-- Active anchor chunk `0` (`m = 256`). -/
def rkmAncPHi_m256_p0 : List RampKickAnchor := [
  ⟨3, [1], [44919386], [5], rkmMasksHi_m256_r3, rkmRowHi_m256_r3⟩,
  ⟨4, [1], [46063982], [6], rkmMasksHi_m256_r4, rkmRowHi_m256_r4⟩,
  ⟨5, [1, 1], [37014165, 9744260], [6, 3], rkmMasksHi_m256_r5, rkmRowHi_m256_r5⟩,
  ⟨6, [1, 1, 1, 1, 1, 1, 1, 1],
    [16831441, 17069434, 5713791, 3094959, 2264590, 1379868, 718544, 160275],
    [9, 9, 1, 1, 1, 1, 1, 1], rkmMasksHi_m256_r6, rkmRowHi_m256_r6⟩,
  ⟨7, [1, 1, 1, 1, 1, 1, 1, 1],
    [20902411, 20967411, 1904582, 1333212, 597294, 711306, 778246, 389118],
    [9, 9, 1, 1, 1, 1, 1, 1], rkmMasksHi_m256_r7, rkmRowHi_m256_r7⟩,
  ⟨8, [1, 1, 1, 1, 1, 1, 1, 1],
    [21193512, 20950515, 1904591, 1033212, 681394, 702706, 807447, 584399],
    [9, 9, 1, 1, 1, 1, 1, 1], rkmMasksHi_m256_r8, rkmRowHi_m256_r8⟩,
  ⟨9, [1, 1, 1, 1, 1, 1, 1, 1],
    [21465057, 22402660, 404592, 901213, 602695, 700207, 864748, 740274],
    [9, 9, 1, 1, 1, 1, 1, 1], rkmMasksHi_m256_r9, rkmRowHi_m256_r9⟩,
  ⟨10, [1, 1, 1, 1, 1, 1, 1, 1],
    [21713584, 22402788, 344612, 721737, 636215, 698927, 887372, 864801],
    [9, 9, 1, 1, 1, 1, 1, 1], rkmMasksHi_m256_r10, rkmRowHi_m256_r10⟩,
  ⟨11, [1, 1, 1, 1, 1, 1, 1, 1],
    [20379255, 22413035, 1880859, 570885, 617759, 697271, 907589, 966651],
    [9, 9, 1, 1, 1, 1, 1, 1], rkmMasksHi_m256_r11, rkmRowHi_m256_r11⟩,
  ⟨12, [1, 1, 1, 1, 1, 1],
    [20386171, 21888871, 2085265, 2369681, 1629666, 220064],
    [10, 10, 1, 1, 1, 1], rkmMasksHi_m256_r12, rkmRowHi_m256_r12⟩
  ]
/-- Active anchor chunk `1` (`m = 256`). -/
def rkmAncPHi_m256_p1 : List RampKickAnchor := [
  ⟨13, [1, 1, 1, 1, 1, 1, 1, 1],
    [21225168, 21597189, 2026620, 1815971, 834547, 462559, 481573, 267305],
    [9, 10, 1, 1, 1, 1, 1, 1], rkmMasksHi_m256_r13, rkmRowHi_m256_r13⟩,
  ⟨14, [1, 1, 1, 1, 1, 1, 1, 1],
    [21225108, 21717154, 1949613, 1852765, 793341, 436097, 540697, 316129],
    [9, 10, 1, 1, 1, 1, 1, 1], rkmMasksHi_m256_r14, rkmRowHi_m256_r14⟩,
  ⟨15, [1, 1, 1, 1, 1, 1, 1, 1],
    [20618603, 22434745, 1883612, 1853285, 791561, 431525, 569827, 358907],
    [9, 10, 1, 1, 1, 1, 1, 1], rkmMasksHi_m256_r15, rkmRowHi_m256_r15⟩,
  ⟨16, [1, 1, 1, 1, 1, 1, 1, 1],
    [23544244, 23560881, 32640, 30237, 701579, 780423, 210257, 185853],
    [10, 10, 1, 1, 1, 1, 1, 1], rkmMasksHi_m256_r16, rkmRowHi_m256_r16⟩,
  ⟨17, [1, 1, 1, 1, 1, 1, 1, 1],
    [21703388, 21552900, 1737454, 1210405, 1544403, 809549, 156299, 429975],
    [11, 12, 1, 1, 1, 1, 1, 1], rkmMasksHi_m256_r17, rkmRowHi_m256_r17⟩,
  ⟨18, [1, 1, 1, 1, 1, 1, 1, 1],
    [21748829, 21601024, 1690378, 1211429, 1539007, 717929, 268974, 460266],
    [11, 12, 1, 1, 1, 1, 1, 1], rkmMasksHi_m256_r18, rkmRowHi_m256_r18⟩,
  ⟨19, [1, 1, 1, 1, 1, 1, 1, 1],
    [20621136, 22520696, 1941262, 1221529, 1512627, 576761, 445438, 487887],
    [11, 12, 1, 1, 1, 1, 1, 1], rkmMasksHi_m256_r19, rkmRowHi_m256_r19⟩,
  ⟨20, [1, 1, 1, 1, 1, 1, 1, 1],
    [20623614, 22604094, 1899461, 1215708, 1557226, 347964, 653437, 511991],
    [11, 12, 1, 1, 1, 1, 1, 1], rkmMasksHi_m256_r20, rkmRowHi_m256_r20⟩,
  ⟨21, [1, 1, 1, 1, 1, 1, 1, 1],
    [20630168, 22677348, 1867034, 1221086, 1526825, 479143, 558413, 536837],
    [11, 12, 1, 1, 1, 1, 1, 1], rkmMasksHi_m256_r21, rkmRowHi_m256_r21⟩,
  ⟨22, [1, 1, 1, 1, 1, 1, 1, 1],
    [20683976, 22689252, 1850042, 1201669, 1593104, 883404, 121364, 554998],
    [11, 12, 1, 1, 1, 1, 1, 1], rkmMasksHi_m256_r22, rkmRowHi_m256_r22⟩
  ]
/-- Active anchor chunk `2` (`m = 256`). -/
def rkmAncPHi_m256_p2 : List RampKickAnchor := [
  ⟨23, [1, 1, 1, 1, 1, 1, 1, 1],
    [20753972, 22625148, 1885259, 1226989, 1527307, 463379, 597464, 577200],
    [11, 12, 1, 1, 1, 1, 1, 1], rkmMasksHi_m256_r23, rkmRowHi_m256_r23⟩,
  ⟨24, [1, 1, 1, 1, 1, 1, 1, 2],
    [22784895, 22503395, 612690, 1345713, 921198, 974485, 590921, 8],
    [15, 15, 1, 1, 1, 1, 1, 1], rkmMasksHi_m256_r24, rkmRowHi_m256_r24⟩,
  ⟨25, [1, 1, 1, 1, 1, 1, 1, 1],
    [22149767, 23188466, 617310, 1336404, 882867, 987714, 463195, 183812],
    [15, 16, 1, 1, 1, 1, 1, 1], rkmMasksHi_m256_r25, rkmRowHi_m256_r25⟩,
  ⟨26, [1, 1, 1, 1, 1, 1, 1, 1],
    [22323869, 23033270, 645615, 1320509, 878972, 995914, 439045, 246712],
    [15, 16, 1, 1, 1, 1, 1, 1], rkmMasksHi_m256_r26, rkmRowHi_m256_r26⟩,
  ⟨27, [1, 1, 1, 1, 1, 1, 1, 1],
    [23057569, 22350570, 637715, 1330109, 884472, 979314, 419943, 297612],
    [15, 16, 1, 1, 1, 1, 1, 1], rkmMasksHi_m256_r27, rkmRowHi_m256_r27⟩,
  ⟨28, [1, 1, 1, 1, 1, 1, 1, 1],
    [23820071, 21636972, 636517, 1334414, 885792, 970934, 423814, 321012],
    [15, 16, 1, 1, 1, 1, 1, 1], rkmMasksHi_m256_r28, rkmRowHi_m256_r28⟩,
  ⟨29, [1, 1, 1, 1, 1, 1, 1, 1],
    [24104671, 21394672, 643917, 1333414, 883992, 973434, 420314, 346412],
    [15, 16, 1, 1, 1, 1, 1, 1], rkmMasksHi_m256_r29, rkmRowHi_m256_r29⟩,
  ⟨30, [1, 1, 1, 1, 1, 1, 1, 1],
    [21415231, 23193716, 1005606, 1271334, 1543377, 872302, 195070, 674702],
    [15, 16, 1, 1, 1, 1, 1, 1], rkmMasksHi_m256_r30, rkmRowHi_m256_r30⟩,
  ⟨31, [1, 1, 1, 1, 1, 1, 1, 1],
    [21625274, 22633204, 1420437, 1313793, 1470364, 972071, 420009, 386660],
    [15, 16, 1, 1, 1, 1, 1, 1], rkmMasksHi_m256_r31, rkmRowHi_m256_r31⟩,
  ⟨32, [1, 1, 1, 1, 1, 1],
    [23488193, 23512805, 1464664, 1143840, 168284, 533376],
    [18, 18, 1, 1, 1, 1], rkmMasksHi_m256_r32, rkmRowHi_m256_r32⟩
  ]
/-- Active anchor chunk `3` (`m = 256`). -/
def rkmAncPHi_m256_p3 : List RampKickAnchor := [
  ⟨48, [1, 1, 1],
    [47500000, 3002400, 896158],
    [48, 3, 1], rkmMasksHiHiB_m256_r48, rkmRowHiHiB_m256_r48⟩,
  ⟨64, [1, 1, 1, 1],
    [25169277, 25205117, 1236244, 895003],
    [33, 33, 2, 2], rkmMasksHiHiB_m256_r64, rkmRowHiHiB_m256_r64⟩,
  ⟨96, [1, 1, 1, 1],
    [16164539, 15975141, 1085917, 793973],
    [31, 31, 3, 2], rkmMasksHiHiB_m256_r96, rkmRowHiHiB_m256_r96⟩,
  ⟨128, [1, 1, 1, 1, 1, 1, 1, 1],
    [18074835, 18006368, 18006368, 1298570, 1459632, 564434, 505143, 165378],
    [44, 44, 44, 4, 4, 2, 2, 1], rkmMasksHiHiB_m256_r128, rkmRowHiHiB_m256_r128⟩,
  ⟨192, [1, 1, 1, 1, 1, 1, 1, 1],
    [14758040, 14702137, 11026603, 1457880, 1638703, 518465, 515558, 153731],
    [50, 50, 38, 5, 6, 2, 2, 1], rkmMasksHiHiB_m256_r192, rkmRowHiHiB_m256_r192⟩,
  ⟨256, [1, 1, 2, 2, 2, 2, 2, 2],
    [13706357, 16281422, 8842647, 8855047, 1086907, 1258412, 808438, 752779],
    [58, 69, 61, 61, 8, 9, 6, 6], rkmMasksHiHiB_m256_r256, rkmRowHiHiB_m256_r256⟩,
  ⟨384, [1, 1, 2, 2, 2, 2, 2, 2],
    [13603415, 16603863, 7422424, 7235899, 653824, 752234, 512749, 606766],
    [77, 94, 71, 70, 7, 8, 5, 6], rkmMasksHiHiB_m256_r384, rkmRowHiHiB_m256_r384⟩,
  ⟨512, [1, 2, 4, 4, 4, 4, 4, 4],
    [12140921, 7408710, 15518271, 1114954, 465966, 542962, 448190, 312671],
    [83, 89, 299, 22, 9, 11, 9, 7], rkmMasksHiHiB_m256_r512, rkmRowHiHiB_m256_r512⟩
  ]
/-- Sorted active multi-segment anchors (`m = 256, kMax = 512`). -/
def rkmAnchorsHi_m256 : List RampKickAnchor :=
  rkmAncPHi_m256_p0 ++ (rkmAncPHi_m256_p1 ++ (rkmAncPHi_m256_p2 ++ rkmAncPHi_m256_p3))
private theorem rkm_anc_app_hi_256 {m0 lMax : ℕ} :
    ∀ {xs ys : List RampKickAnchor},
      RampKickAnchorsSound m0 lMax xs → RampKickAnchorsSound m0 lMax ys →
      RampKickAnchorsSound m0 lMax (xs ++ ys)
  | [], _, _, hy => hy
  | _ :: _, _, ⟨hx0, hxs⟩, hy =>
      ⟨hx0, rkm_anc_app_hi_256 hxs hy⟩
private theorem rkmAncSndPHi_m256_p0 : RampKickAnchorsSound 256 32 rkmAncPHi_m256_p0 :=
  ⟨rkmTrajHi_m256_r3, ⟨rkmTrajHi_m256_r4, ⟨rkmTrajHi_m256_r5, ⟨rkmTrajHi_m256_r6,
    ⟨rkmTrajHi_m256_r7, ⟨rkmTrajHi_m256_r8, ⟨rkmTrajHi_m256_r9, ⟨rkmTrajHi_m256_r10,
    ⟨rkmTrajHi_m256_r11, ⟨rkmTrajHi_m256_r12, trivial⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
private theorem rkmAncSndPHi_m256_p1 : RampKickAnchorsSound 256 32 rkmAncPHi_m256_p1 :=
  ⟨rkmTrajHi_m256_r13, ⟨rkmTrajHi_m256_r14, ⟨rkmTrajHi_m256_r15, ⟨rkmTrajHi_m256_r16,
    ⟨rkmTrajHi_m256_r17, ⟨rkmTrajHi_m256_r18, ⟨rkmTrajHi_m256_r19, ⟨rkmTrajHi_m256_r20,
    ⟨rkmTrajHi_m256_r21, ⟨rkmTrajHi_m256_r22, trivial⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
private theorem rkmAncSndPHi_m256_p2 : RampKickAnchorsSound 256 32 rkmAncPHi_m256_p2 :=
  ⟨rkmTrajHi_m256_r23, ⟨rkmTrajHi_m256_r24, ⟨rkmTrajHi_m256_r25, ⟨rkmTrajHi_m256_r26,
    ⟨rkmTrajHi_m256_r27, ⟨rkmTrajHi_m256_r28, ⟨rkmTrajHi_m256_r29, ⟨rkmTrajHi_m256_r30,
    ⟨rkmTrajHi_m256_r31, ⟨rkmTrajHi_m256_r32, trivial⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
private theorem rkmAncSndPHi_m256_p3 : RampKickAnchorsSound 256 32 rkmAncPHi_m256_p3 :=
  ⟨rkmTrajHiHiB_m256_r48, ⟨rkmTrajHiHiB_m256_r64, ⟨rkmTrajHiHiB_m256_r96,
    ⟨rkmTrajHiHiB_m256_r128, ⟨rkmTrajHiHiB_m256_r192, ⟨rkmTrajHiHiB_m256_r256,
    ⟨rkmTrajHiHiB_m256_r384, ⟨rkmTrajHiHiB_m256_r512, trivial⟩⟩⟩⟩⟩⟩⟩⟩
/-- Anchor trajectory soundness bundle (`m = 256, kMax = 512`). -/
theorem rkmAnchorsSoundHi_m256 :
    RampKickAnchorsSound 256 32 rkmAnchorsHi_m256 :=
  rkm_anc_app_hi_256 rkmAncSndPHi_m256_p0 (rkm_anc_app_hi_256 rkmAncSndPHi_m256_p1
    (rkm_anc_app_hi_256 rkmAncSndPHi_m256_p2 rkmAncSndPHi_m256_p3))
private def rkmAtF : List Bool → Bool
  | [] => true | true :: bs => rkmAtF bs | false :: _ => false
private theorem rkmHd {b : Bool} {bs : List Bool} (h : rkmAtF (b :: bs) = true) :
    b = true := by cases b with | false => exact Bool.noConfusion h | true => rfl
private theorem t1 {b : Bool} {bs : List Bool} (h : rkmAtF (b :: bs) = true) :
    rkmAtF bs = true := by cases b with | false => exact Bool.noConfusion h | true => exact h
private theorem t2 {a b : Bool} {bs : List Bool}
    (h : rkmAtF (a :: b :: bs) = true) : rkmAtF bs = true := t1 (t1 h)
private theorem t4 {a b c d : Bool} {bs : List Bool}
    (h : rkmAtF (a :: b :: c :: d :: bs) = true) : rkmAtF bs = true := t2 (t2 h)
private theorem t8 {a b c d e f g i : Bool} {bs : List Bool}
    (h : rkmAtF (a :: b :: c :: d :: e :: f :: g :: i :: bs) = true) :
    rkmAtF bs = true := t4 (t4 h)
private theorem rkm_bf {b : Bool} (h : Bool.not b = true) : b = false := by
  cases b with | false => rfl | true => cases h
private def rkmRevOnto : List ℕ → List ℕ → List ℕ
  | [], acc => acc | x :: xs, acc => rkmRevOnto xs (x :: acc)
private def rkmCapEnd : ℕ → List ℕ → ℕ
  | vc, [] => vc | vc, x :: xs => rkmCapEnd (cond (primNatBlt vc x) x vc) xs
private def rkmTailGeB (n : ℕ) : List RampKickAnchor → Bool
  | [] => true | b :: _ => n.ble b.rAct
private def rkmHead2Eq (v1 : ℕ) : List ℕ → Bool
  | a :: b :: _ => cond (a.beq 0) (b.beq v1) false | _ => false
private theorem rkm_beq_eq : ∀ {a b : ℕ}, a.beq b = true → a = b
  | 0, 0, _ => rfl | 0, _ + 1, h => Bool.noConfusion h | _ + 1, 0, h => Bool.noConfusion h
  | _ + 1, _ + 1, h => congrArg Nat.succ (rkm_beq_eq h)
private theorem rkm_nat_beq_false : ∀ (a b : ℕ), a ≠ b → a.beq b = false
  | 0, 0, h => absurd rfl h | 0, _ + 1, _ => rfl | _ + 1, 0, _ => rfl
  | a + 1, b + 1, h => rkm_nat_beq_false a b (fun e => h (congrArg Nat.succ e))
private theorem rkm_head2_append {v1 : ℕ} :
    ∀ (xs ys : List ℕ), rkmHead2Eq v1 xs = true → xs ++ ys = 0 :: v1 :: (xs.drop 2 ++ ys)
  | a :: b :: _, _, h => by
    dsimp only [rkmHead2Eq] at h; cases ha : a.beq 0 with
    | false => rw [ha] at h; cases h | true => rw [ha] at h; rw [rkm_beq_eq ha, rkm_beq_eq h]; rfl
  | [], _, h => Bool.noConfusion h | [_], _, h => Bool.noConfusion h
private theorem rkm_le_of_ble : ∀ {a b : ℕ}, a.ble b = true → a ≤ b
  | 0, _, _ => Nat.zero_le _ | _ + 1, 0, h => Bool.noConfusion h
  | _ + 1, _ + 1, h => Nat.succ_le_succ (rkm_le_of_ble h)
private theorem rkm_blt_false_of_le {a b : ℕ} (h : a ≤ b) : primNatBlt b a = false := by
  unfold primNatBlt; rw [← Bool.not_eq_true]; intro ht
  have hle := rkm_le_of_ble ht; simp only [Nat.add_eq] at hle; omega
private theorem rkm_cond_imp_right {c t1 t2 : Bool} (h : cond c t1 false = true)
    (ht : t1 = true → t2 = true) : cond c t2 false = true := by
  cases c with | false => cases h | true => exact ht h
private theorem rkm_cond_imp_left_false {c b1 b2 : Bool} (h : cond c false b1 = true)
    (hb : b1 = true → b2 = true) : cond c false b2 = true := by
  cases c with | false => exact hb h | true => cases h
private theorem rkm_cond_imp_both {c a1 a2 b1 b2 : Bool} (h : cond c a1 b1 = true)
    (ha : a1 = true → a2 = true) (hb : b1 = true → b2 = true) : cond c a2 b2 = true := by
  cases c with | false => exact hb h | true => exact ha h
private theorem rkm_cond_skip2_imp {c1 c2 d f t1 t2 : Bool} (hc1 : c1 = false) (hc2 : c2 = false)
    (h : cond f t1 false = true) (ht : t1 = true → t2 = true) :
    cond c1 false (cond c2 d (cond f t2 false)) = true := by
  rw [hc1, hc2]; exact rkm_cond_imp_right h ht
private theorem rkm_aux_split (m lMax : ℕ) (uc : Bool) :
    ∀ (xs ys : List ℕ) (r r' vc vc' : ℕ) (vh : List ℕ) (as bs : List RampKickAnchor),
      Nat.add r (altListLen xs) = r' → rkmCapEnd vc xs = vc' → rkmTailGeB r' bs = true →
      rkmCheckTableAux m lMax uc xs r vc vh as = true →
      rkmCheckTableAux m lMax uc ys r' vc' (rkmRevOnto xs vh) bs = true →
      rkmCheckTableAux m lMax uc (xs ++ ys) r vc vh (as ++ bs) = true
  | [], _, r, r', vc, vc', _, as, _, hr, hvc, _, hx, hy => by
    cases as with | nil => subst hr; subst hvc; exact hy | cons _ _ => cases hx
  | vR :: xRest, ys, r, r', vc, vc', vh, as, bs, hr, hvc, hbs, hx, hy => by
    cases vh with | nil => cases hx | cons vPrev vhRest =>
      let r1 := Nat.add r 1; let vc1 := cond (primNatBlt vc vR) vR vc
      let vh1 := vR :: vPrev :: vhRest
      have hr' : Nat.add r1 (altListLen xRest) = r' := by
        simp only [r1, Nat.add_eq, rkmb_altListLen_eq, List.length_cons] at hr ⊢; omega
      cases as with
      | cons a aRest =>
        dsimp only [List.cons_append]; unfold rkmCheckTableAux at hx ⊢
        simp only [rkmb_forceNat_eq] at hx ⊢
        refine rkm_cond_imp_left_false hx fun hx1 => rkm_cond_imp_both hx1 (fun hd => ?_) ?_
        · exact rkm_cond_imp_right hd fun hrec =>
            rkm_aux_split m lMax uc xRest ys r1 r' vc1 vc' vh1 aRest bs hr' hvc hbs hrec hy
        · exact fun hf => rkm_cond_imp_right hf fun hrec =>
            rkm_aux_split m lMax uc xRest ys r1 r' vc1 vc' vh1 (a :: aRest) bs hr' hvc hbs hrec hy
      | nil =>
        cases bs with
        | nil =>
          dsimp only [List.cons_append, List.nil_append]; unfold rkmCheckTableAux at hx ⊢
          simp only [rkmb_forceNat_eq] at hx ⊢
          exact rkm_cond_imp_right hx fun hrec =>
            rkm_aux_split m lMax uc xRest ys r1 r' vc1 vc' vh1 [] [] hr' hvc rfl hrec hy
        | cons b bsRest =>
          dsimp only [List.cons_append, List.nil_append]; unfold rkmCheckTableAux at hx ⊢
          simp only [rkmb_forceNat_eq] at hx ⊢
          have hb_ge : r' ≤ b.rAct := rkm_le_of_ble hbs
          have hr_lt : r < r' := by
            simp only [Nat.add_eq, rkmb_altListLen_eq, List.length_cons] at hr; omega
          have hlt : primNatBlt b.rAct r = false := rkm_blt_false_of_le (by omega)
          have heq : b.rAct.beq r = false := rkm_nat_beq_false b.rAct r (by omega)
          exact rkm_cond_skip2_imp hlt heq hx fun hrec =>
            rkm_aux_split m lMax uc xRest ys r1 r' vc1 vc' vh1 [] (b :: bsRest) hr' hvc hbs hrec hy
private def rkmOuterGuard256 : Bool :=
  Bool.or (primNatBlt 256 1) (Bool.or (primNatBlt 32 1)
    (Bool.or (primNatBlt 8192 (Nat.mul 32 256)) (Bool.or (primNatBlt 512 2)
      (Bool.or (primNatBlt 1024 512)
        (Bool.not ((altListLen rkmVPotHi_m256).beq (Nat.add 512 1)))))))
private theorem rkm_table_of_parts_256 (v1 : ℕ) (vRest : List ℕ)
    (hg : rkmOuterGuard256 = false) (hvPot : rkmVPotHi_m256 = 0 :: v1 :: vRest)
    (heig : checkEigStep 256 1 v1 0 = true)
    (haux : rkmCheckTableAux 256 32 true vRest 2 v1 [v1, 0] rkmAnchorsHi_m256 = true) :
    rkmCheckTable 256 512 32 true rkmVPotHi_m256 rkmAnchorsHi_m256 = true := by
  unfold rkmCheckTable; unfold rkmOuterGuard256 at hg; rw [hg, hvPot]; dsimp only
  rw [heig, haux]; rfl
private theorem rkm_take_drop_eq {α : Type} :
    ∀ (k : ℕ) (xs : List α), xs.take k ++ xs.drop k = xs
  | 0, _ => rfl | _ + 1, [] => rfl
  | k + 1, x :: xs => congrArg (x :: ·) (rkm_take_drop_eq k xs)
private def rkmVc0 : List ℕ := (rkmVPotHi_m256_p0.drop 2).take 63
private def rkmVc1 : List ℕ := (rkmVPotHi_m256_p0.drop 2).drop 63
private def rkmVc2 : List ℕ := rkmVPotHi_m256_p1.take 64
private def rkmVc3 : List ℕ := rkmVPotHi_m256_p1.drop 64
private def rkmVc4 : List ℕ := rkmVPotHi_m256_p2.take 64
private def rkmVc5 : List ℕ := rkmVPotHi_m256_p2.drop 64
private def rkmVc6 : List ℕ := rkmVPotHi_m256_p3.take 64
private def rkmVc7 : List ℕ := rkmVPotHi_m256_p3.drop 64
private def rkmVh1 : List ℕ := rkmRevOnto rkmVc0 [40168692606172, 0]
private def rkmVh2 : List ℕ := rkmRevOnto rkmVc1 rkmVh1
private def rkmVh3 : List ℕ := rkmRevOnto rkmVc2 rkmVh2
private def rkmVh4 : List ℕ := rkmRevOnto rkmVc3 rkmVh3
private def rkmVh5 : List ℕ := rkmRevOnto rkmVc4 rkmVh4
private def rkmVh6 : List ℕ := rkmRevOnto rkmVc5 rkmVh5
private def rkmVh7 : List ℕ := rkmRevOnto rkmVc6 rkmVh6
private def rkmAt1 : List RampKickAnchor := rkmAncPHi_m256_p3.drop 2
private def rkmAt2 : List RampKickAnchor := rkmAt1.drop 2
private def rkmAt3 : List RampKickAnchor := rkmAt2.drop 1
private def rkmAt4 : List RampKickAnchor := rkmAt3.drop 1
private def rkmAnc7 : List RampKickAnchor := rkmAt4.drop 1
private def rkmAnc5 : List RampKickAnchor := rkmAt4.take 1
private def rkmAnc3 : List RampKickAnchor := rkmAt3.take 1
private def rkmAnc2 : List RampKickAnchor := rkmAt2.take 1
private def rkmAnc1 : List RampKickAnchor := rkmAt1.take 2
private def rkmAnc0 : List RampKickAnchor :=
  rkmAncPHi_m256_p0 ++ (rkmAncPHi_m256_p1 ++ (rkmAncPHi_m256_p2 ++
    rkmAncPHi_m256_p3.take 2))
private def rkmAbs5 : List RampKickAnchor := rkmAnc5 ++ rkmAnc7
private def rkmAbs3 : List RampKickAnchor := rkmAnc3 ++ rkmAbs5
private def rkmAbs2 : List RampKickAnchor := rkmAnc2 ++ rkmAbs3
private def rkmAbs1 : List RampKickAnchor := rkmAnc1 ++ rkmAbs2
private abbrev rkmP0 : Prop := rkmAtF [
  Bool.not rkmOuterGuard256, rkmHead2Eq 40168692606172 rkmVPotHi_m256_p0,
  checkEigStep 256 1 40168692606172 0, (Nat.add 2 (altListLen rkmVc0)).beq 65,
  (rkmCapEnd 40168692606172 rkmVc0).beq 146222115477001, rkmTailGeB 65 rkmAbs1,
  rkmCheckTableAux 256 32 true rkmVc0 2 40168692606172 [40168692606172, 0] rkmAnc0] = true
private theorem rkmC0 : rkmP0 := by decide +kernel
private abbrev rkmP1 : Prop := rkmAtF [
  (Nat.add 65 (altListLen rkmVc1)).beq 129,
  (rkmCapEnd 146222115477001 rkmVc1).beq 202610414633589,
  rkmTailGeB 129 rkmAbs2,
  rkmCheckTableAux 256 32 true rkmVc1 65 146222115477001
    rkmVh1 rkmAnc1] = true
private theorem rkmC1 : rkmP1 := by decide +kernel
private abbrev rkmP2 : Prop := rkmAtF [
  (Nat.add 129 (altListLen rkmVc2)).beq 193,
  (rkmCapEnd 202610414633589 rkmVc2).beq 259293179448470,
  rkmTailGeB 193 rkmAbs3,
  rkmCheckTableAux 256 32 true rkmVc2 129 202610414633589
    rkmVh2 rkmAnc2] = true
private theorem rkmC2 : rkmP2 := by decide +kernel
private abbrev rkmP3 : Prop := rkmAtF [
  (Nat.add 193 (altListLen rkmVc3)).beq 258,
  (rkmCapEnd 259293179448470 rkmVc3).beq 264793299837302,
  rkmTailGeB 258 rkmAbs5,
  rkmCheckTableAux 256 32 true rkmVc3 193 259293179448470
    rkmVh3 rkmAnc3] = true
private theorem rkmC3 : rkmP3 := by decide +kernel
private abbrev rkmP4 : Prop := rkmAtF [
  (Nat.add 258 (altListLen rkmVc4)).beq 322,
  (rkmCapEnd 264793299837302 rkmVc4).beq 264793299837302,
  rkmTailGeB 322 rkmAbs5,
  rkmCheckTableAux 256 32 true rkmVc4 258 264793299837302
    rkmVh4 []] = true
private theorem rkmC4 : rkmP4 := by decide +kernel
private abbrev rkmP5 : Prop := rkmAtF [
  (Nat.add 322 (altListLen rkmVc5)).beq 387,
  (rkmCapEnd 264793299837302 rkmVc5).beq 360467869824471,
  rkmTailGeB 387 rkmAnc7,
  rkmCheckTableAux 256 32 true rkmVc5 322 264793299837302
    rkmVh5 rkmAnc5] = true
private theorem rkmC5 : rkmP5 := by decide +kernel
private abbrev rkmP6 : Prop := rkmAtF [
  (Nat.add 387 (altListLen rkmVc6)).beq 451,
  (rkmCapEnd 360467869824471 rkmVc6).beq 360467869824471,
  rkmTailGeB 451 rkmAnc7,
  rkmCheckTableAux 256 32 true rkmVc6 387 360467869824471
    rkmVh6 []] = true
private theorem rkmC6 : rkmP6 := by decide +kernel
private abbrev rkmP7 : Prop :=
  rkmCheckTableAux 256 32 true rkmVc7 451 360467869824471 rkmVh7 rkmAnc7 = true
private theorem rkmC7 : rkmP7 := by decide +kernel
private abbrev rkmBp0 : Prop := rkmAtF [
  rkmCheckAnchorsLMax 2 1 rkmAnchorsHi_m256, rkmCheckAnchorsLMax 2 2 rkmAnchorsHi_m256,
  checkAltBound12 256 2 (rkmVPotHi_m256.getD 2 0) 257046901743 500000000000,
  rkmCheckAnchorsLMax 4 1 rkmAnchorsHi_m256, rkmCheckAnchorsLMax 4 2 rkmAnchorsHi_m256,
  checkAltBound12 256 4 (rkmVPotHi_m256.getD 4 0) 174409850017 500000000000,
  rkmCheckAnchorsLMax 8 1 rkmAnchorsHi_m256, rkmCheckAnchorsLMax 8 2 rkmAnchorsHi_m256,
  checkAltBound12 256 8 (rkmVPotHi_m256.getD 8 0) 11071331 48828125] = true
private theorem rkmBc0 : rkmBp0 := by decide +kernel
private abbrev rkmBp1 : Prop := rkmAtF [
  rkmCheckAnchorsLMax 16 1 rkmAnchorsHi_m256, rkmCheckAnchorsLMax 16 2 rkmAnchorsHi_m256,
  checkAltBound12 256 16 (rkmVPotHi_m256.getD 16 0) 75590974927 500000000000,
  rkmCheckAnchorsLMax 32 2 rkmAnchorsHi_m256, rkmCheckAnchorsLMax 32 2 rkmAnchorsHi_m256,
  checkAltBound12 256 32 (rkmVPotHi_m256.getD 32 0) 51772670317 500000000000,
  rkmCheckAnchorsLMax 64 2 rkmAnchorsHi_m256, rkmCheckAnchorsLMax 64 2 rkmAnchorsHi_m256,
  checkAltBound12 256 64 (rkmVPotHi_m256.getD 64 0) 36721497027 500000000000] = true
private theorem rkmBc1 : rkmBp1 := by decide +kernel
private abbrev rkmBp2 : Prop := rkmAtF [
  rkmCheckAnchorsLMax 128 2 rkmAnchorsHi_m256, rkmCheckAnchorsLMax 128 2 rkmAnchorsHi_m256,
  checkAltBound12 256 128 (rkmVPotHi_m256.getD 128 0) 55938748033 1000000000000,
  rkmCheckAnchorsLMax 256 2 rkmAnchorsHi_m256, rkmCheckAnchorsLMax 256 2 rkmAnchorsHi_m256,
  checkAltBound12 256 256 (rkmVPotHi_m256.getD 256 0) 48066079 976562500,
  rkmCheckAnchorsLMax 512 4 rkmAnchorsHi_m256, rkmCheckAnchorsLMax 512 4 rkmAnchorsHi_m256,
  checkAltBound12 256 512 (rkmVPotHi_m256.getD 512 0) 9386381389 200000000000] = true
private theorem rkmBc2 : rkmBp2 := by decide +kernel
/-- Kernel Bellman table verification (`m = 256, kMax = 512`). -/
theorem rkmTableOkHi_m256 :
    rkmCheckTable 256 512 32 true rkmVPotHi_m256 rkmAnchorsHi_m256 = true := by
  let s6 := rkmVc6 ++ rkmVc7; let s5 := rkmVc5 ++ s6; let s4 := rkmVc4 ++ s5
  let s3 := rkmVc3 ++ s4; let s2 := rkmVc2 ++ s3; let s1 := rkmVc1 ++ s2
  let s0 := rkmVc0 ++ s1
  have h6 := rkm_aux_split 256 32 true rkmVc6 rkmVc7 387 451
    360467869824471 360467869824471 rkmVh6 [] rkmAnc7 (rkm_beq_eq (rkmHd rkmC6))
    (rkm_beq_eq (rkmHd (t1 rkmC6))) (rkmHd (t2 rkmC6)) (rkmHd (t1 (t2 rkmC6))) rkmC7
  have h5 := rkm_aux_split 256 32 true rkmVc5 s6 322 387
    264793299837302 360467869824471 rkmVh5 rkmAnc5 rkmAnc7 (rkm_beq_eq (rkmHd rkmC5))
    (rkm_beq_eq (rkmHd (t1 rkmC5))) (rkmHd (t2 rkmC5)) (rkmHd (t1 (t2 rkmC5))) h6
  have h4 := rkm_aux_split 256 32 true rkmVc4 s5 258 322
    264793299837302 264793299837302 rkmVh4 [] rkmAbs5 (rkm_beq_eq (rkmHd rkmC4))
    (rkm_beq_eq (rkmHd (t1 rkmC4))) (rkmHd (t2 rkmC4)) (rkmHd (t1 (t2 rkmC4))) h5
  have h3 := rkm_aux_split 256 32 true rkmVc3 s4 193 258
    259293179448470 264793299837302 rkmVh3 rkmAnc3 rkmAbs5 (rkm_beq_eq (rkmHd rkmC3))
    (rkm_beq_eq (rkmHd (t1 rkmC3))) (rkmHd (t2 rkmC3)) (rkmHd (t1 (t2 rkmC3))) h4
  have h2 := rkm_aux_split 256 32 true rkmVc2 s3 129 193
    202610414633589 259293179448470 rkmVh2 rkmAnc2 rkmAbs3 (rkm_beq_eq (rkmHd rkmC2))
    (rkm_beq_eq (rkmHd (t1 rkmC2))) (rkmHd (t2 rkmC2)) (rkmHd (t1 (t2 rkmC2))) h3
  have h1 := rkm_aux_split 256 32 true rkmVc1 s2 65 129
    146222115477001 202610414633589 rkmVh1 rkmAnc1 rkmAbs2 (rkm_beq_eq (rkmHd rkmC1))
    (rkm_beq_eq (rkmHd (t1 rkmC1))) (rkmHd (t2 rkmC1)) (rkmHd (t1 (t2 rkmC1))) h2
  have h0 := rkm_aux_split 256 32 true rkmVc0 s1 2 65 40168692606172 146222115477001
    [40168692606172, 0] rkmAnc0 rkmAbs1 (rkm_beq_eq (rkmHd (t1 (t2 rkmC0))))
    (rkm_beq_eq (rkmHd (t4 rkmC0))) (rkmHd (t1 (t4 rkmC0)))
    (rkmHd (t2 (t4 rkmC0))) h1
  have ha5 : rkmAbs5 = rkmAt4 := rkm_take_drop_eq 1 rkmAt4
  have ha3 : rkmAbs3 = rkmAt3 := by unfold rkmAbs3 rkmAnc3; rw [ha5]; exact rkm_take_drop_eq 1 _
  have ha2 : rkmAbs2 = rkmAt2 := by unfold rkmAbs2 rkmAnc2; rw [ha3]; exact rkm_take_drop_eq 1 _
  have ha1 : rkmAbs1 = rkmAt1 := by unfold rkmAbs1 rkmAnc1; rw [ha2]; exact rkm_take_drop_eq 2 _
  have h_anc_eq : rkmAnc0 ++ rkmAbs1 = rkmAnchorsHi_m256 := by
    unfold rkmAnc0 rkmAnchorsHi_m256; rw [ha1]; unfold rkmAt1
    rw [List.append_assoc, List.append_assoc, List.append_assoc, rkm_take_drop_eq 2 _]
  have hs6 : s6 = rkmVPotHi_m256_p3 := rkm_take_drop_eq 64 rkmVPotHi_m256_p3
  have hs4 : s4 = rkmVPotHi_m256_p2 ++ rkmVPotHi_m256_p3 := by
    dsimp only [s4, s5, rkmVc4, rkmVc5]; rw [← List.append_assoc, rkm_take_drop_eq 64 _, hs6]
  have hs2 : s2 = rkmVPotHi_m256_p1 ++ (rkmVPotHi_m256_p2 ++ rkmVPotHi_m256_p3) := by
    dsimp only [s2, s3, rkmVc2, rkmVc3]; rw [← List.append_assoc, rkm_take_drop_eq 64 _, hs4]
  have hs0 : s0 = rkmVPotHi_m256_p0.drop 2 ++
      (rkmVPotHi_m256_p1 ++ (rkmVPotHi_m256_p2 ++ rkmVPotHi_m256_p3)) := by
    dsimp only [s0, s1, rkmVc0, rkmVc1]; rw [← List.append_assoc, rkm_take_drop_eq 63 _, hs2]
  have hvPot : rkmVPotHi_m256 = 0 :: 40168692606172 :: s0 := by
    unfold rkmVPotHi_m256; rw [hs0]; exact rkm_head2_append _ _ (rkmHd (t1 rkmC0))
  rw [h_anc_eq] at h0
  exact rkm_table_of_parts_256 40168692606172 s0 (rkm_bf (rkmHd rkmC0))
    hvPot (rkmHd (t2 rkmC0)) h0
/-- Unpacked `RampKickTableValid` bundle (`m = 256, kMax = 512`). -/
theorem rkmValidHi_m256 :
    RampKickTableValid 256 512 32 true rkmVPotHi_m256 rkmAnchorsHi_m256 :=
  rkmCheckTable_sound rkmTableOkHi_m256 rkmAnchorsSoundHi_m256
/-- Cell `lMax = 1` bound for `(256, 2)`. -/
theorem rkmCellLMaxHi_m256_k2 :
    rkmCheckAnchorsLMax 2 1 rkmAnchorsHi_m256 = true :=
  rkmHd rkmBc0
/-- Cold-`r2` `lMax = 2` (`>= 2`) bound for `(256, 2)`. -/
theorem rkmCellLMax2Hi_m256_k2 :
    rkmCheckAnchorsLMax 2 2 rkmAnchorsHi_m256 = true :=
  rkmHd (t1 rkmBc0)
/-- Relative-cost certificate `257046901743 / 500000000000` for `(256, 2)`. -/
theorem rkmBoundHi_m256_k2 :
    checkAltBound12 256 2 (rkmVPotHi_m256.getD 2 0) 257046901743 500000000000 = true :=
  rkmHd (t2 rkmBc0)
/-- Cell `lMax = 1` bound for `(256, 4)`. -/
theorem rkmCellLMaxHi_m256_k4 :
    rkmCheckAnchorsLMax 4 1 rkmAnchorsHi_m256 = true :=
  rkmHd (t1 (t2 rkmBc0))
/-- Cold-`r2` `lMax = 2` (`>= 2`) bound for `(256, 4)`. -/
theorem rkmCellLMax2Hi_m256_k4 :
    rkmCheckAnchorsLMax 4 2 rkmAnchorsHi_m256 = true :=
  rkmHd (t4 rkmBc0)
/-- Relative-cost certificate `174409850017 / 500000000000` for `(256, 4)`. -/
theorem rkmBoundHi_m256_k4 :
    checkAltBound12 256 4 (rkmVPotHi_m256.getD 4 0) 174409850017 500000000000 = true :=
  rkmHd (t1 (t4 rkmBc0))
/-- Cell `lMax = 1` bound for `(256, 8)`. -/
theorem rkmCellLMaxHi_m256_k8 :
    rkmCheckAnchorsLMax 8 1 rkmAnchorsHi_m256 = true :=
  rkmHd (t2 (t4 rkmBc0))
/-- Cold-`r2` `lMax = 2` (`>= 2`) bound for `(256, 8)`. -/
theorem rkmCellLMax2Hi_m256_k8 :
    rkmCheckAnchorsLMax 8 2 rkmAnchorsHi_m256 = true :=
  rkmHd (t1 (t2 (t4 rkmBc0)))
/-- Relative-cost certificate `11071331 / 48828125` for `(256, 8)`. -/
theorem rkmBoundHi_m256_k8 :
    checkAltBound12 256 8 (rkmVPotHi_m256.getD 8 0) 11071331 48828125 = true :=
  rkmHd (t8 rkmBc0)
/-- Cell `lMax = 1` bound for `(256, 16)`. -/
theorem rkmCellLMaxHi_m256_k16 :
    rkmCheckAnchorsLMax 16 1 rkmAnchorsHi_m256 = true :=
  rkmHd rkmBc1
/-- Cold-`r2` `lMax = 2` (`>= 2`) bound for `(256, 16)`. -/
theorem rkmCellLMax2Hi_m256_k16 :
    rkmCheckAnchorsLMax 16 2 rkmAnchorsHi_m256 = true :=
  rkmHd (t1 rkmBc1)
/-- Relative-cost certificate `75590974927 / 500000000000` for `(256, 16)`. -/
theorem rkmBoundHi_m256_k16 :
    checkAltBound12 256 16 (rkmVPotHi_m256.getD 16 0) 75590974927 500000000000 = true :=
  rkmHd (t2 rkmBc1)
/-- Cell `lMax = 2` bound for `(256, 32)`. -/
theorem rkmCellLMaxHi_m256_k32 :
    rkmCheckAnchorsLMax 32 2 rkmAnchorsHi_m256 = true :=
  rkmHd (t1 (t2 rkmBc1))
/-- Cold-`r2` `lMax = 2` (`>= 2`) bound for `(256, 32)`. -/
theorem rkmCellLMax2Hi_m256_k32 :
    rkmCheckAnchorsLMax 32 2 rkmAnchorsHi_m256 = true :=
  rkmHd (t4 rkmBc1)
/-- Relative-cost certificate `51772670317 / 500000000000` for `(256, 32)`. -/
theorem rkmBoundHi_m256_k32 :
    checkAltBound12 256 32 (rkmVPotHi_m256.getD 32 0) 51772670317 500000000000 = true :=
  rkmHd (t1 (t4 rkmBc1))
/-- Cell `lMax = 2` bound for `(256, 64)`. -/
theorem rkmCellLMaxHi_m256_k64 :
    rkmCheckAnchorsLMax 64 2 rkmAnchorsHi_m256 = true :=
  rkmHd (t2 (t4 rkmBc1))
/-- Cold-`r2` `lMax = 2` (`>= 2`) bound for `(256, 64)`. -/
theorem rkmCellLMax2Hi_m256_k64 :
    rkmCheckAnchorsLMax 64 2 rkmAnchorsHi_m256 = true :=
  rkmHd (t1 (t2 (t4 rkmBc1)))
/-- Relative-cost certificate `36721497027 / 500000000000` for `(256, 64)`. -/
theorem rkmBoundHi_m256_k64 :
    checkAltBound12 256 64 (rkmVPotHi_m256.getD 64 0) 36721497027 500000000000 = true :=
  rkmHd (t8 rkmBc1)
/-- Cell `lMax = 2` bound for `(256, 128)`. -/
theorem rkmCellLMaxHi_m256_k128 :
    rkmCheckAnchorsLMax 128 2 rkmAnchorsHi_m256 = true :=
  rkmHd rkmBc2
/-- Cold-`r2` `lMax = 2` (`>= 2`) bound for `(256, 128)`. -/
theorem rkmCellLMax2Hi_m256_k128 :
    rkmCheckAnchorsLMax 128 2 rkmAnchorsHi_m256 = true :=
  rkmHd (t1 rkmBc2)
/-- Relative-cost certificate `55938748033 / 1000000000000` for `(256, 128)`. -/
theorem rkmBoundHi_m256_k128 :
    checkAltBound12 256 128 (rkmVPotHi_m256.getD 128 0) 55938748033 1000000000000 = true :=
  rkmHd (t2 rkmBc2)
/-- Cell `lMax = 2` bound for `(256, 256)`. -/
theorem rkmCellLMaxHi_m256_k256 :
    rkmCheckAnchorsLMax 256 2 rkmAnchorsHi_m256 = true :=
  rkmHd (t1 (t2 rkmBc2))
/-- Cold-`r2` `lMax = 2` (`>= 2`) bound for `(256, 256)`. -/
theorem rkmCellLMax2Hi_m256_k256 :
    rkmCheckAnchorsLMax 256 2 rkmAnchorsHi_m256 = true :=
  rkmHd (t4 rkmBc2)
/-- Relative-cost certificate `48066079 / 976562500` for `(256, 256)`. -/
theorem rkmBoundHi_m256_k256 :
    checkAltBound12 256 256 (rkmVPotHi_m256.getD 256 0) 48066079 976562500 = true :=
  rkmHd (t1 (t4 rkmBc2))
/-- Cell `lMax = 4` bound for `(256, 512)`. -/
theorem rkmCellLMaxHi_m256_k512 :
    rkmCheckAnchorsLMax 512 4 rkmAnchorsHi_m256 = true :=
  rkmHd (t2 (t4 rkmBc2))
/-- Cold-`r2` `lMax = 4` (`>= 2`) bound for `(256, 512)`. -/
theorem rkmCellLMax2Hi_m256_k512 :
    rkmCheckAnchorsLMax 512 4 rkmAnchorsHi_m256 = true :=
  rkmHd (t1 (t2 (t4 rkmBc2)))
/-- Relative-cost certificate `9386381389 / 200000000000` for `(256, 512)`. -/
theorem rkmBoundHi_m256_k512 :
    checkAltBound12 256 512 (rkmVPotHi_m256.getD 512 0) 9386381389 200000000000 = true :=
  rkmHd (t8 rkmBc2)

/-- Terminal `1`-lane table closure for `FindAllJohnsonRampKickMuxHiCert256`. -/
theorem laneClosure_FindAllJohnsonRampKickMuxHiCert256 :
    rkmTrajHiHiB_m256_r512 = rkmTrajHiHiB_m256_r512 :=
  (And.intro (Eq.refl laneWitness_FindAllJohnsonRampKickMuxHi256T8) rfl).right

end
end QuantumComputation.Specs.DickeSol
