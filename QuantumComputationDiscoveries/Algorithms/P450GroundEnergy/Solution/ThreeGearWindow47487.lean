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

public import QuantumComputationDiscoveries.Algorithms.P450GroundEnergy.Solution.ThreeGearWindow47487Aux
public import QuantumComputationDiscoveries.Algorithms.P450GroundEnergy.Solution.SevenGearBondDeferB

/-!
# Certified Window & Error-Budget Companion `(M = 47,487, mLow = 7)` (`ThreeGearWindow47487`)

Provides `regData_47487_7` (`tWin = 142,248`), `regData_47487_7_ok`, `threeGearWin_47487_10_7`,
and `threeGearWinCirc_47487_10_7`.

## References
- A. Luis and J. Peřina, *Phys. Rev. A* **54**, 4564 (1996), DOI: 10.1103/PhysRevA.54.4564.
- M. Möttönen et al., *Phys. Rev. Lett.* **93**, 130502 (2004), DOI: 10.1103/PhysRevLett.93.130502.
- R. Babbush et al., *Phys. Rev. X* **8**, 041015 (2018), DOI: 10.1103/PhysRevX.8.041015.
- J. Lee et al., *PRX Quantum* **2**, 030305 (2021), DOI: 10.1103/PRXQuantum.2.030305.
-/

@[expose] public section

namespace QuantumComputationSpecs.Algorithms.P450GroundEnergy.Solution.TwoGearQPEPhase5
open QuantumComputation.Specs QuantumComputation.Specs.P450

/-- Certified Two-Gear regime data for `(M, mLow) = (47487, 7)` (`tWin = 142248`). -/
@[noinline] def regData_47487_7 : TwoGearRegimeData where
  M := 47487
  mLow := 7
  D := 371
  mHi := 9
  c0Mid := 999999999452931133627288
  s0Mid := 33077752832472456844
  a0Nat := 73422090469580306581492
  a1Nat := 179473094333142955992
  b0Nat := 125000373443219752313303
  b1Nat := 51137407318800316622619120
  eHiNum := 2266376507174
  eLo0Num := 7073164674
  eLo1Num := 156354339704
  tWin := 142248
  hiTrees := [
    (rP 0xbf1ab015c440 0xe38fe 125 0x1a66c0996027cba8f5156c75f3356e09 0x25),
    (wBr (rP 0xf2661b3cbba4 0xe38e3 124 0x5bbb66e97a0fbf0a3de186314e52ad6 0x0) (rP
    0xf2661b3cbba4 0xe38e3 124 0x5bbb66e97a0fbf0a3de186314e52ad6 0x0)),
    (wBr (wBr (rP 0x1686d7244ff06 0x1c71fd7b 125 0x110b75fa43617df51f82e52d8472c08 0x0) (rN
    0x26871a19b7b 0x69f3 124 0xce2e95dbb0ea5cf8512c78e0bd54052 0x0)) (wBr (rP 0x63654fc8b0be
    0x38e3d7b 123 0x4e1092e2740f9dbf9b31b7b8fd2fa50 0x0) (rP 0x5e8669608a04 0x3e 124
    0xc76db48b13bde0a378f5ac5298722d7 0x4))),
    (wBr (wBr (wBr (rP 0x162ab3eb58694 0x27df3 125 0x32767b60e040383318866c0ec5e9d47 0x25) (rP
    0x18d40f8fcb3e 0xe3d1e 122 0xc6b1e58fe759c4baf51e5dc9e754e0 0x0)) (wBr wSk (rP
    0x34fb50ab4759 0x6 124 0x895f79613b4ac937cfe83f6c194dd93 0x0))) (wBr (wBr (rP 0x4f05903ac84c
    0x38e3d33 125 0x1dbb2c717267df93fd0bc9debc3d9b34 0x25) (rP 0x10966775978d 0x39a3 125
    0xb1f9cc2b1128f45267472c9f4c6c8f3 0x25)) (wBr (rP 0x3f96540ec1f6 0x1c71fd7b 127
    0x2569c02c41fe4bfc3498031444718024 0x0) (rN 0x1cacba80c42d 0x13e9f3 124
    0xd6684fe7c7871e1d952dd799e90141e 0x4)))),
    (wBr (wBr (wBr (wBr (rP 0x157756289662b 0x1c77b 122 0x261b35a059083e136bee9168cbf959e 0x5)
    (rP 0xc6cc7e3c209 0x1a3 126 0xbd34f48fdc569ae72c4501f0b15da0d 0x4)) (wBr (rP 0xab55f3ab4a8
    0x38e3d33 123 0x4e353c51bc299eb67fd5e49143da0a9 0x25) (rN 0x69b201172c7 0x71c733 124
    0xc45be5ae1d7c44d1f8f35cc9c7d92c 0x0))) (wBr (wBr (rP 0x657907d9039 0x9a3 125
    0x1f4dbb40c51cb41d671753b6f79f0e1d 0x5) (rP 0x24312bc02eaa 0x38f47bb 123
    0x14657e8cab0877ff35413be17796948 0x5)) (wBr (rP 0x3a73a07dd461 0x1c7a3 123
    0x3a34c44d03e2c436774fe8a4f45f6c2 0x25) (rN 0x68927946d83 0x69f3 124
    0x138eaab71a78ad2b3c7e4fc46000d4b 0x4)))) (wBr (wBr (wBr (rP 0x4441e3a18614 0x38e3d3e 125
    0x5365c0a96c98cb915b519a0620cee95 0x5) (rP 0x709e066882f 0x38e39f3 126
    0x352ddfe94b508fa56f13b1d75e3fac5c 0x4)) (wBr (rP 0x12ef0e3440e5 0x13e9f3 124
    0xe312e32394ec1f233c3882d7320cbdf 0x4) (rP 0x13b7deb0f9bb 0xfa3 121
    0x11cfc66a099533a873394a383271751 0x25))) (wBr (wBr (rP 0x22eaadd5137a 0x1c71e9f3 125
    0xb9531305a2ff624fc2f178a6f8a3b7c 0x5) (rN 0x1542021ffd26 0x7d3b 125
    0x1e5c110c1b7912ebcbd4b12bd9d1bc6b 0x25)) (wBr (rN 0x25825f8675a2 0x1c71cfbe 126
    0x15b8bf3f6985d3c549e00085a6e4238b 0x0) (rP 0x13c9d91c0cb0 0x1bb 124
    0x7d6db731d55422213906b19f279b9e5 0x0))))),
    (wBr (wBr (wBr (wBr (wBr (rP 0x1562ca3026dc7 0x38e3d33 123 0xe402cd8a57919b52d086855a51dc46
    0x5) (rP 0x4a1fa470ec1 0x38e39bb 128 0x1991a847f47dad7542e9c1091052ba01 0x4)) (wBr (rP
    0x5155cde36b8 0x6 124 0x24cbf94d16fc44e870f6d01e6827f67 0x0) (rN 0x266292bd3e0 0x4d3e 126
    0x5dfe15b947408beaec36d777bda5e8b 0x4))) (wBr (wBr (rN 0x3f68703ccaa 0x9a6 124
    0x528b558658c280d09d6667a87f75d23 0x4) (rN 0x300a9f340db 0x3eb3b 122
    0x393863d764f96815d5ed74318c4739d 0x25)) (wBr (rN 0x671527ce03f 0x4d33 125
    0x152339cfaf9ca2e7cec779e3d2bfc050 0x25) (rP 0x8cd05b2b8b5 0x38f477b 123
    0x3b450b12352e8837ae8589e455444 0x0)))) (wBr (wBr (wBr (rP 0xbbb3f9f1474 0x38f477b 126
    0x35954b2a81d95c0082e79bb4d2e289ff 0x5) (rP 0x1353ff9e8029 0x33 123
    0x2d33c22f3172a17734d5fbeb3fd4346 0x5)) (wBr (rP 0x227f87c70b79 0x1c71e 123
    0x58fb372645dc5b7ff601ae6e7b0985f 0x5) (rN 0x26366fce5d7 0x4fbb 126
    0x1a2906fd650ded28e0fa4d5d2ff6e1cd 0x0))) (wBr (wBr (rP 0x36fc4f317b51 0x3e9f3 124
    0x8e0fedc70c20755937e6d2a9756d124 0x4) (rN 0x2fbd8e41f1f 0xe38f3 121
    0x12cce0b6e6f70888ed76f68f1b202a8 0x25)) (wBr (rN 0x668112a5740 0xe38fb 125
    0x25865b5f8d22add27776b10f3719504 0x25) (rP 0x8c1af43aaa9 0x11c7a3 127
    0x12f9cddffe6416bf199752495dab5edb 0x5))))) (wBr (wBr (wBr (wBr (rP 0x367f23df39f5 0x23 124
    0x756c53324e362bd513185b0c4b53aac 0x0) (rP 0x4c587b74f75 0x1c71cfbe 123
    0x239d39d21d5ff2240affc6a25228909 0x5)) (wBr (rP 0x920a28d3dd8 0xe38e7df3 124
    0x425cf360ca2779ea3b5beca757aca0e 0x4) (rP 0x9208419037c 0x3e 126
    0x34aff3e1ff10e06deaa743479eea694f 0x4))) (wBr (wBr (rP 0x179259bbad4c 0x3 124
    0x38fd95e7d01cb6072ae1ff3006f3bbc 0x4) (rP 0xabf27ea4422 0x1c7a3 123
    0x1155084bf5523a2d3ad1c092a9c95ed 0x25)) (wBr (rP 0x116b6faffde6 0x1c71e 124
    0x61f39f0deeaea4404a8c833914bce3a 0x0) (rN 0x249fad44db5 0x71e8fb 126
    0x3455f255c78e0b088993f0550abb9e73 0x4)))) (wBr (wBr (wBr (rP 0xdc2dd7a8157 0x1c7f477b 125
    0x1aaacf7e44d1f269ed68e13d8168dff6 0x4) (rN 0xb13f8bbeb6d 0x4d7b 125
    0x1035e4ee46cc657ad0205a927af53a7 0x0)) (wBr (rN 0x168ff3bd8e97 0x39a3 122
    0x15c1537d808d23d0aa449359a96cdf3 0x4) (rP 0x9234658eb29 0x27df3 123
    0x3a3ce669b108ac74418dfdb1aebda3c 0x25))) (wBr (wBr (rN 0x27be4c4466fb 0x1c71cdf3 122
    0x30d775b99d6cbc6fad7b4ab472888bb 0x4) (rP 0xac3f92220fe 0x71c7bb 121
    0x6d70a4bdf95bd8faa971130d276389 0x5)) (wBr (rP 0x1174b1c33879 0x27d3b 126
    0x210881224d69ff14d2dd9c038157544a 0x4) (rN 0x2555102efe0 0x27df3 125
    0xdd29fbe31e52c304d4e399242cf7279 0x5)))))),
    (wBr (wBr (wBr (wBr (wBr (wBr (rP 0x15a8336beb839 0x1c71e 124
    0x995f2d5437f9958b926cf1a758de84e 0x4) (rP 0x12fb45934db 0x7d3e 125
    0x22e453d1a303d9b34378de30f02960e 0x25)) (wBr (rP 0x48b72f7ef56 0x1c71e9f3 124
    0xf37af8ffffaa9cd752237cb2686bc7d 0x0) (rP 0x2c30c1d72d8 0xb3b 126
    0x17371ec51796ca28d3c7a08bffad5d84 0x5))) (wBr (wBr wSk (rP 0x15b41ac6132 0x38fe8fb 128
    0xed6d6962bd94a7ce59ea72ad2f40ad06 0x0)) (wBr (rN 0x4f7d19e8d01 0x9a6 126
    0x195b816cc843f059e6f3e0eb02a13e57 0x4) (rP 0x5a5b824b0b 0x38e39f3 124
    0xd8e8b199e4569c9e0b90d10f7f729e 0x4)))) (wBr (wBr (wBr (rN 0xa1f9d67d954 0x71c7a3 121
    0x8875fd3505c1252f284d4fc1e34ded 0x5) (rP 0x12a69681fcb 0xe38fb 125
    0x144ae96e7ff29c72d64071ff484746cb 0x5)) (wBr (rN 0x54e688b01c9 0x38e3d7b 123
    0x315b2408966689e221a5dc9987b4fe1 0x4) (rP 0x9355f20951 0x71e8fb 126
    0xe9e6b70eb10e7c126f326407d3d37f1 0x4))) (wBr (wBr (rN 0x7dce5b9ee75 0x71e8f3 123
    0x551f36c4f5188ce19ebc1742712a5d5 0x25) (rP 0x34d70ba97cf 0x6b3b 124
    0xdb7bb9eb0d625d80d815fcc682c2949 0x5)) (wBr (rP 0xa61254b3aca 0x71c7f3 128
    0xf022a2eee489a0cfb77a7a7e7d08d814 0x4) (rP 0x2e5275386de 0x38e3 127
    0x1524d5da2b2c6e9e409f7aea0a67d793 0x5))))) (wBr (wBr (wBr (wBr (rP 0x79bafee27ab 0x9bb 128
    0x5106aaad6d1f53722e1f1ed79aed57e7 0x4) (rP 0x583f1891601 0x9a3 124
    0xfa2231ae1bed755a1b800d5d8e184cd 0x0)) (wBr (rP 0x1388a4f39b11 0x6b3b 125
    0x1b500cda102e931845de56f3b26b6878 0x4) (rP 0x2c3c94aa063 0x38fe 128
    0xa706cf6bce8cfcc2a8a99507cd7af418 0x4))) (wBr (wBr (rP 0x21e0dd970d9b 0x38e39bb 123
    0x4204f13d4b6759aaf4b1c15325aaf55 0x5) (rP 0x15b41ac6135 0x71e8fb 128
    0xfe81846d4f7143dfd3ad81b41242d260 0x4)) (wBr (rN 0x4f66d510fcd 0x38fe8fb 125
    0x17f9163a049a0f92c65de6f5cbfc9f08 0x5) (rP 0x5a5b824b08 0x38e39f3 124
    0xd8e8b199e4569c9e0b90d10f7f729e 0x4)))) (wBr (wBr (wBr (rP 0x31ed72e314e4 0xe38fb 126
    0x42189a1c493c8e01509bf6688baae5f 0x4) (rP 0x12a69681fd0 0xe38fb 125
    0x144ae96e7ff29c72d64071ff484746cb 0x5)) (wBr (rN 0x54bfb0e364d 0x27d3e 121
    0x2fa325b5181e30343c07b9564af902 0x25) (rP 0x9355f2094b 0x71e8fb 126
    0xe9e6b70eb10e7c126f326407d3d37f1 0x4))) (wBr (wBr (rN 0x7d83bfb1dc0 0x38e3d33 119
    0x56cc0b88edbcf9baf47236fb7420fc 0x25) (rP 0x1a3db8b7a65 0x1c7a3 126
    0x3631e70dbf1ea3573ad6a4bc111e3dd 0x0)) (wBr (rP 0xa5b6effab6a 0xe3d1e 125
    0x13634995ffc6db19d5c0edbe72074b06 0x5) (rP 0x2e559bd25cf 0x8e3d7b 121
    0x14eaa30f4c7a876e039e1d4ca8032b1 0x4)))))) (wBr (wBr (wBr (wBr (wBr (rP 0x28d7d8e52c51
    0x1f3 126 0x2ffd9cdc1f8a2b046c06c5375abe85d5 0x0) (rP 0x36ee58f9f7e 0x38e3df3 124
    0x63073065e67a583ed3f5cb1c4cb55f9 0x0)) (wBr (rP 0x2663a6de29d 0x38e3fbe 124
    0x4cf2d144639ec8d6c90f256f7613e34 0x0) (rP 0xa07666a955 0x38e3fa3 126
    0x2d5cf2a6866ea5f15728b226fa2caa 0x4))) (wBr (wBr (rP 0x9808cde93d4 0x71c7a6 125
    0x670bf6ea3475a17c7e2948fe9a7dae1 0x25) (rP 0x28fb9f1218d 0xe38e6 125
    0x1515e831cfa74ce558d3a2de2a0d84d 0x5)) (wBr (rP 0xa8bd8bdc288 0x4fa3 123
    0x29b02b6adfe34b6607196dc2f7bbe55 0x5) (rP 0x2e40ce96d47 0x133 125
    0x1c488084841fd030fc00d2f4cdd5276b 0x5)))) (wBr (wBr (wBr (rP 0x165f42074f69 0xf47a3 125
    0x29e4bfec6ec692e981fe0b8d272ef4a 0x5) (rP 0x3087eccb31a 0x0 124
    0xde9e6b9ad065483540f421b31349665 0x0)) (wBr (rP 0xb6a811dfc51 0x8e3d7b 124
    0xebc22d68da75b3ac7fe552b9854703f 0x25) (rP 0x2c83b6b59f8 0x1c71cd7b 123
    0x6e5a5e83093f67bc1f19011b13e864b 0x0))) (wBr (wBr (rP 0xfbd87349781 0x1c71eb3b 123
    0x1f9e51b8e2505ae52fb1d4fc9cf29a4 0x0) (rP 0x8f11e09554 0x38e3d33 126
    0x608a89ec9fe1f1ecc780931cf5fd48 0x4)) (wBr (rN 0x4e953aeff13 0x71e8fb 124
    0xb29b98da46f7efb4bbc2f99ead485ec 0x0) (rP 0x53751e9626 0x4fa3 126
    0x9c04ccdc06b6fc56dc08d80489c6b3b 0x0))))) (wBr (wBr (wBr (wBr (rP 0x7978a33ec86 0x269f3 126
    0x21f03675f05390df643c8c27dd61829f 0x0) (rN 0x12fb4595e42 0x38e3fa3 124
    0x88783b1c13fdd1fdc95df79a8be3f19 0x0)) (wBr (rN 0xd2abc9aa683 0x38e3fa3 123
    0x755adcbe7b3e26332c1defd0410a923 0x25) (rP 0xa07666a956 0x38e3fa3 126
    0x2d5cf2a6866ea5f15728b226fa2caa 0x4))) (wBr (wBr (rN 0x198348fa25d3 0xfbe 126
    0x989cc0051b6c5cbca2c1689832a9716 0x0) (rP 0x29122beaa45 0xe3d1e 125
    0x16b9ef01c97fd596af8a2da225ac5296 0x25)) (wBr (rP 0xa8d3d14cd12 0x38fe8f3 122
    0x1e49eb71f6cf1d974af7503b24f9f1e 0x0) (rP 0x2e2535a20da 0x4fbe 124
    0x7880dde661f991f25d48d9804d71a8 0x0)))) (wBr (wBr (wBr (rN 0x27dcf0d60175 0x7df3 125
    0x1620bcb8033dfd87ef129f55a81f9a25 0x5) (rP 0x30af34a3e23 0x3e 126
    0x3752f74b848cf6f2ef13cb9593303f42 0x4)) (wBr (rP 0xb6ceeae762e 0x13b 123
    0x15f90e022e16a3b57289147d443423e 0x5) (rP 0x2c539cbed70 0x71c7bb 121
    0xa9f6559c02b06180df87cd3b1b154e 0x25))) (wBr (wBr (rP 0xfc2313840d5 0x38e3fa3 122
    0x38159c9f5b583adcc9dbd785ff4b9f9 0x0) (rP 0x232e0afc772 0xd3e 122
    0x404c57775c224a3bd6793eb0f20043 0x4)) (wBr (rN 0x4ef09d4e072 0xe38e7d7b 121
    0x77facb1b1cc2f42af0741a12ee736b 0x0) (rP 0x53751e9627 0x4fa3 126
    0x9c04ccdc06b6fc56dc08d80489c6b3b 0x0))))))),
    (wBr (wBr (wBr (wBr (wBr (wBr (wBr (rP 0x169dc6a59c01c 0x269f3 122
    0x30ad4cc4ce2431dc4dd7617f04a302a 0x4) (rP 0x1a4c523642e 0x38fe8fb 126
    0x3e7d8e36a74a7ae0dffe0917b9739beb 0x4)) (wBr (rP 0x1494db020 0x0 121
    0x350c972799a53bd6c74fe4f8a3da96 0x5) (rP 0xa5d7a8f827 0x38e3fa3 121
    0x521bb4ebe50dbde5ca75743289a15a 0x5))) (wBr (wBr (rP 0x4abc7d76b3f 0x1be 125
    0xd058d44a16d9f39c6d6e6affcfdee00 0x25) (rP 0x143b8348086 0x7d3b 126
    0x2f0d82b60ef77a1669e2ebcfcc8a9ac9 0x0)) (wBr (rP 0x2bddc90ca7e 0x9a3 123
    0x7027dc1b209c9f553cda735e189de44 0x5) (rP 0x87df0f5826 0x1c71e 123
    0x5c8fa37127cd0325963c3085193e022 0x5)))) (wBr (wBr (wBr wSk (rP 0xb085bf433c 0x38e39f3 124
    0x274c892cc6ff82a78ac78f7585e37a0 0x0)) (wBr (rP 0x1d48009e551 0xdf3 123
    0x6ba1f533d418a5f0248ec59246f560 0x5) (rP 0x1022fd43d39 0x39a3 120
    0x446c508aba09b13714f10d0a8c1ca 0x4))) (wBr (wBr (rN 0x3fbb09d8801 0x1be 125
    0xe9796ea262d58898fd9683007609350 0x25) (rP 0xa0d1f6dd87 0x1c71e 114
    0x39878abf3a7db96351884fabc7cf8 0x4)) (wBr (rN 0x14bcd9a3dd 0xe38fb 123
    0x17d155db2f7388975b9b88ad11e9b6e 0x25) (rP 0x11a9b05e396 0x38e39bb 126
    0x270f1565acbb878568cc1fe9b3c09ee5 0x0))))) (wBr (wBr (wBr (wBr (rN 0xc75a8216cb4 0x7d3e 124
    0x283f8535c8397841e8c946d9059287 0x0) (rP 0xa33118fa0c 0x71c7bb 126
    0x378779b06ef17a6f4a6f8f9e937c251f 0x4)) (wBr (rP 0x1bb07ec776b 0x1c71cdf3 125
    0x1695ae42833043e0e1d6e9c31d4bda90 0x5) (rP 0x10b243334dd 0x4fbb 124
    0xd59fb851c49901a590030493bb56fef 0x4))) (wBr (wBr (rN 0x42865d6dd8e 0x13e 125
    0x4a6dfa7f93347c06e195c526674cd20 0x5) (rP 0xb050f2dbf7 0x38e3d7b 123
    0x2b4492be9e0831fcef8fa202b263dd3 0x0)) (wBr (rP 0x8c4b28812 0xd3b 118
    0x3d9095cf0a13bd88c625a57deaaeca 0x4) (rP 0x117389de6b5 0x1bb 125
    0xbf8a7c7e9f00ed244fb78a92018e08a 0x25)))) (wBr (wBr (wBr (rN 0x5aed4d45caf 0xe3d1e 121
    0x17122be7e7c5ec114781761d0cf0111 0x5) (rP 0x166617b03be 0x26 125
    0x1f4f7ba5d29c548b1208eb80e77631d2 0x25)) (wBr (rP 0x13472518126 0xfa3 126
    0x1d1898d6c564ff9be90e772ef0b8033a 0x0) (rP 0xab6873a1b9 0x4d3e 120
    0x111c048b5c1007f4ac388e367182a5 0x0))) (wBr (wBr (rP 0x7e2324fdcee 0x1c71cd7b 122
    0x19d1362460a79453615ce88e28e70ff 0x25) (rP 0x14d154dc44e 0x38e3fa6 124
    0x425cd0ef478c99707bcbb4435988c61 0x0)) (wBr (rP 0x2cfac5e5cee 0x69f3 126
    0x27d98f7bdbacbefc7142a54a44145e55 0x0) (rP 0x817e56dbc0 0x4d7b 122
    0x613744e0995bea8e09561d6293c7ea 0x25)))))) (wBr (wBr (wBr (wBr (wBr wP0 (rP 0x19b76306599
    0x71e 124 0xe5f1fd983b61ab4a9e60e4cdc103791 0x0)) (wBr (rP 0x34a71ed1092 0x38e39bb 122
    0x2182e43e9f66f667839a59fc3377772 0x0) (rP 0xa5e3b72289 0x17b 123
    0x2d2a175e8c5fbb86b159ab33abf0186 0x0))) (wBr (wBr (rP 0xcc6762d0ad1 0x9bb 125
    0xaced95ed1ea039e1296f3e1705f8b60 0x5) (rP 0x143cffddc03 0x38e3 124
    0x274f067d812439d5bfb5ae938235db6 0x4)) (wBr (rP 0x2be3b62c1e7 0x13eb3b 123
    0x1dc12996292f5fd2e260426f8173097 0x0) (rP 0x87d0500c42 0x71e8fb 130
    0x1cb7721faa636a7c367ba6c0f8547f3bc 0x0)))) (wBr (wBr (wBr (rP 0x16e27cda344a 0x1c71cfbe 125
    0x1c130faf980be9309b19541b74e609d 0x5) (rP 0xb0b31976f7 0x38e3df3 124
    0x3a44200bc45ba3f695da9fe15553b4e 0x0)) (wBr (rP 0x1d4da72b9ce 0x27df3 126
    0x1c731d58f15c2da812bdef285e5396cb 0x0) (rP 0x10213b8d046 0x11c7a3 127
    0xb0639de0f0da7b10b9aca1b862fc1b6 0x25))) (wBr (wBr (rN 0x3fafe0f432e 0x71fd1e 124
    0x3e2615e5b462627efed7a78a729d06f 0x0) (rP 0xa09a769778 0xdf3 122
    0x2dc7d8333a425332576795e95157cca 0x0)) (wBr (rN 0x14bcd9a3dd 0xe38fb 123
    0x17d155db2f7388975b9b88ad11e9b6e 0x25) (rP 0x11a9c2a056f 0x6 121
    0x16933723fd394e61c2400709d2dfae8 0x5))))) (wBr (wBr (wBr (wBr (rP 0x2655b182b5aa 0x23 123
    0x4df422f7a0b3f52789aeeb35393f08f 0x25) (rP 0xa3800c2ee8 0x9a3 124
    0xb940a457c75e5146d058b88b02f1338 0x4)) (wBr (rP 0x1bba55dd1d9 0x38e3d7b 123
    0x7e2d5c8b951d7c66900f3531463d465 0x4) (rP 0x10af34efd00 0x38e39f3 126
    0xa503898cdfe305beff1e3f0e75199bd 0x4))) (wBr (wBr (rN 0x4272e79393b 0x7d3e 124
    0xc3ff625b782261f37112e3bd6ce497 0x0) (rP 0xaff045cdbb 0x7d3b 125
    0x1e4cab653fbcca53d2aa49e13c34834 0x25)) (wBr (rP 0x8c4b28812 0xd3b 118
    0x3d9095cf0a13bd88c625a57deaaeca 0x4) (rP 0x1173a640905 0x4d3b 124
    0x6ffb86769eee20663ba1be11cd17485 0x0)))) (wBr (wBr (wBr (rN 0x5ac7ed5071f 0x38e3d3e 125
    0xf1570274260520ef6b197554d9385da 0x25) (rP 0x165a7e26e3a 0x4d3b 121
    0xbc16c6c1ea29061a945d28c4f15bae 0x25)) (wBr (rP 0x1330026170a 0xe38fb 125
    0x1fac46a03298282aa1425409aec3215e 0x5) (rP 0xab6bb5e305 0x38f47a3 125
    0x1fb901c97e4b000070ba9d92f52c3219 0x5))) (wBr (wBr (rP 0x7df55cf386d 0x71c733 125
    0x1f0445b49e589f85a937feabb514d7b6 0x25) (rP 0x14d1babc59c 0x38e39be 125
    0xd9d2b83819931f546c97687db12e8a7 0x25)) (wBr (rP 0x2cfc5af8329 0x4fbe 125
    0x140c2e19691550615a73969a646d3c3 0x5) (rP 0x817a5ec575 0xe3 126
    0x34e3d97cf7271c2c2aa9cc1601c946dd 0x4))))))) (wBr (wBr (wBr (wBr (wBr (wBr (rP
    0x155bb7495337 0x38fe8fb 126 0x15e5abe7a7e9c018d342c9bb2bd8a243 0x4) (rP 0xa540e4d0d0
    0x71c73b 123 0x4394d6d85e6522d1394ac7d84d1d924 0x25)) (wBr (rP 0x36d13b46908 0x1c71fdf3 126
    0xa8e4c5fb3ee3e56ff838996ac2bdca6 0x4) (rP 0x10cbeb2213c 0x1c71cdf3 118
    0x36c0432b404aa78f6808276de1d813 0x4))) (wBr (wBr wP0 (rP 0xb369b3bbd4 0x269f3 126
    0x6f75d3fd10fc28051300945cb998d99 0x0)) (wBr (rP 0xf5fdaf8a0 0x38f47a3 126
    0x257b8ae64ae671644536c5716bbf6dcb 0x4) (rP 0x11713e04025 0x1c71e 123
    0x7624241f5ff44513ad6f8c252d1acb3 0x5)))) (wBr (wBr (wBr (rP 0x5f933a93f00 0x71c7a6 121
    0xd107f599f3d7fa74873f28e64d6f30 0x5) (rP 0x16bf4c62511 0x7d3b 123
    0x2a18552606708a23cb7bb6a8563ea42 0x5)) (wBr (rP 0x13f81b822a9 0x38e39bb 126
    0x2979a116e1a18883003913f03d075c 0x4) (rP 0xab2f2a5285 0xfbb 126
    0x3cf4fab396e532022da2a44337d05a0b 0x0))) (wBr (wBr (rP 0x7f7ab7806fa 0x71c7a3 126
    0x2350dbc64e73785433433ead6e312c87 0x4) (rP 0x14cabd3ef4f 0x27d3b 125
    0x28e88b51c615935a0731d13755f4886 0x25)) (wBr (rP 0x2cf1bc76cff 0x38e3fa3 124
    0x6b7552070934832c38fa364b8e30f1 0x0) (rP 0x81d2f95375 0x6 126
    0x77d7313b259314ea94dd2a51ce203fa 0x0))))) (wBr (wBr (wBr (wBr (rP 0x13d014b595db 0xe3 123
    0x74896fd1d111979a03ca547b6af5455 0x25) (rP 0x18bd06ca7e5 0x38fe8fb 126
    0x15b0dea16e75ba22553ed412b1c8ee5d 0x0)) (wBr (rP 0x17d67f5ccce 0x71fd1e 126
    0xdc91c6e224dc3fa9c83b362033fda6c 0x0) (rP 0xa668b1e403 0x1c71cd7b 125
    0x971bf81da471b66457ccd27bc4191b2 0x4))) (wBr (wBr (rP 0x86938907ce2 0x9a6 120
    0x38142fdd64726350546bedd02b4d96 0x0) (rP 0x144cdbba9f3 0xe38fb 126
    0x22eb06b279fbc29f87c48382bfb7a917 0x4)) (wBr (rP 0x2c079459644 0x71c7a6 124
    0x4a7fb36aa09da692621a33200f3bb9d 0x0) (rP 0x874d0e47b5 0xfbb 124
    0x91b6d00a5c7b828338210d6fa7b1ab8 0x4)))) (wBr (wBr (wBr (rP 0xad7c6067a13 0x23 125
    0x166c953b16d4c626de550ffcde288464 0x25) (rP 0xb26f39317d 0x71c7f3 126
    0x387b65bf6e05e3b1d625525b1fb35574 0x4)) (wBr (rP 0x1d849064595 0x8e3d7b 125
    0x8c43faa952cbd50805a68bbe32a054 0x4) (rP 0x10133d58ad4 0x1c71e9f3 124
    0x2d27873a4400b18adf52d12c2c5ec93 0x4))) (wBr (wBr (rN 0x3f464291103 0x69f3 124
    0x8e00965bb69ca8b695de58a89c45e79 0x0) (rP 0x9eefd66e3d 0x7d3e 124
    0x73451134fe7e1972c5cd613f2a57652 0x4)) (wBr (rN 0x18383a89e8 0xfbe 118
    0xdfacdbe1e418bd7a09ca89a946fd 0x0) (rP 0x11abea3f007 0x1c7a3d7b 120
    0xdca48e2ded898e4d7e907550621eef 0x25)))))) (wBr (wBr (wBr (wBr (wBr (rP 0x8d489892bc7
    0x38e3b3b 123 0x1be6cdaeecd3c7a155d5fe3a2857f12 0x4) (rP 0x9bf1f37abf 0x1f3 124
    0x5aa7b984c156c41a4147da26ea7b789 0x0)) (wBr (rN 0x1494db020 0xfa6 121
    0xdf80a8a9fc9f55b0b11342895febc1 0x25) (rP 0x10ccac04c45 0x38fe8f3 126
    0x3d2b0feacd0402c936d8df184e8123eb 0x0))) (wBr (wBr (rN 0x864b7543bdd 0x11c7a3 127
    0x6d891bc17502b04b0224289e4313188 0x5) (rP 0xb3817d153a 0x71fd7b 124
    0xfcd51d6e523f69e710622285398185a 0x25)) (wBr (rP 0xf5fdaf8a0 0x38f47a3 126
    0x257b8ae64ae671644536c5716bbf6dcb 0x4) (rP 0x1170520f332 0x7df3 128
    0x4226cd0dce00c2b9d54b52266fd90440 0x0)))) (wBr (wBr (wBr (rN 0x117b45e9896c 0xe3fa3 126
    0xf94876b074c6a608b1848272017413d 0x4) (rP 0x16c22205e5a 0x38fe8f3 122
    0x2893d31493e71383e61a674c5ac154f 0x0)) (wBr (rP 0x13fdc20ea4f 0x38e3fbe 124
    0x688cb3ddd17799d0c0876f32b903531 0x4) (rP 0xab130ee6d7 0x3e 123
    0x635a204dc1da996c3ca4a92e0f2d97a 0x25))) (wBr (wBr (rP 0x7f85e08edd8 0x38e3d3e 126
    0x19a45e18e07375521fd50f5c1b5f5f18 0x4) (rP 0x14c7453a390 0x38e3fa3 125
    0x1b62bc5f363e79e5c4774a8a172a6cd1 0x25)) (wBr (rP 0x2ce3e7db981 0x9a3 117
    0x16ee7473d797f0a5503b994c22594a 0x25) (rP 0x81d41d7538 0x38e39bb 124
    0xf757eb4385a8a5828e18cd2b180e6f0 0x0))))) (wBr (wBr (wBr (wBr (rN 0x2013c29c9c47 0x38f477b
    124 0xb1034fd17f1501e710daa515803b980 0x25) (rP 0x18c1f5fe92c 0x27d7b 123
    0x40e6f151aa15abbe778e1e0a9bbd1fa 0x4)) (wBr (rP 0x17e05671d8f 0x269f3 126
    0x31b9f239410c33be37dd5a8dbf13bb0f 0x4) (rP 0xa637cdaeba 0x4fa3 121
    0x934586dd693aabb0ca5e0f768cca63 0x5))) (wBr (wBr (rP 0x86a6ff34967 0x1f3 125
    0x652ecf41a04178b46f9fc36e8841103 0x25) (rP 0x1446d0e9305 0x27d3b 126
    0x26116f8c59a67f8094ea1852aed75db 0x4)) (wBr (rP 0x2bef7adbdf0 0x27d3b 125
    0x19067973560bc8981e432883c034dbed 0x5) (rP 0x874ed469e5 0x4df3 125
    0x18da544fc2cf3a0267a8ee96ab4f9c2f 0x5)))) (wBr (wBr (wBr (rP 0xada1c159ea8 0x7d33 123
    0x39ff89bebd8c9776931906795a83871 0x25) (rP 0xb1b5a0b19d 0x133 119
    0x3ab9f14046c1628e120f0dbc81949e 0x25)) (wBr (rP 0x1d6d6daa256 0x38e3df3 126
    0x334e48d0dc94ce5c6a8f3b2f18c5dc56 0x4) (rP 0x1013717cc44 0x13b 126
    0x3c9d05913072b737d3c52e2a3a7b88aa 0x4))) (wBr (wBr (rN 0x3f7409f321c 0x17b 123
    0x4bdcb45d767351bc0623e0619fc8b39 0x4) (rP 0x9ef6346ee2 0x26 126
    0x11b0e70a95e68901d669c2b8357ff65f 0x4)) (wBr (rN 0x18383a89e8 0xfbe 118
    0xdfacdbe1e418bd7a09ca89a946fd 0x0) (rP 0x11abaabd96f 0x4fa3 124
    0x237f24e026515762be6e4bee01202da 0x0)))))))),
    regTree_47487_7_0,
    (wBr regTree_47487_7_1 regTree_47487_7_2)]
  loTrees := [
    (wBr (rP 0x10c1f7cd1038c 0x1c7f477b 125 0x1d5fa4d21f20f1d785db267f2e50b417 0x0) (rP
    0x60c8ddf1e790 0x1a3 123 0x67a76e82e104318c49f8e464eba1f16 0x5)),
    (wBr (wBr (rP 0x12c9d70cb51f2 0x38e3d33 123 0x496d3f55787d4001d56173d1f2bd3dc 0x5) (rP
    0x1da1937715e3 0x13b 124 0xee59d80f6408dead477c06db71e86c7 0x0)) (wBr (rP 0x42f1f6623f98
    0x133 126 0xcbf3164d772dfc202a09c04a5871fcc 0x0) (rN 0x1da182c08d7b 0xe3d1e 125
    0x15c972961aaadb3bfc4aac54eb1497cc 0x25))),
    (wBr (wBr (wBr (rP 0x14721bee31a97 0x38fe 122 0x3260e6685de01dd3c8df7cc053ce03e 0x4) (rP
    0x106f608f0590 0x69f3 125 0x1d37587c17b502046ab982916b374326 0x5)) (wBr (rP 0x17bfb748ba41
    0x38e3fa3 123 0x3e97e7b058b8b11c51e5ff7e892ec2f 0x5) (rN 0xd3bc5dc2717 0x1c71fdf3 123
    0x5f59cf0f60ce6563bb130a1d9d7fd74 0x25))) (wBr (wBr (rP 0x2b29af8c6df4 0x38f47a3 125
    0x19e6e683cf60836db2ff1ba6a6b9b8bd 0x25) (rN 0x106f5c622c40 0x26b3b 124
    0x20db0bb401022159b23c86ce4ebc987 0x5)) (wBr (rN 0x17bfaeee458f 0x9be 126
    0xc9122d8ddff37a7fc98fbe46061c222 0x4) (rP 0xd3bc5dc2851 0x38e3d7b 123
    0x7ae92ea0745d2b58ee5e2eecea2a0cb 0x4)))),
    (wBr (wBr (wBr (wBr (rP 0x15a0456cd911d 0x4df3 124 0xc9021f4899b14f489b748701dec6d83 0x0)
    (rP 0x8b19cbe4161 0x3 126 0x29e383f4c622fe1c76f41936138e3777 0x0)) (wBr (rP 0xcbfaf967117
    0x71c7f3 124 0xaba69f8ac6079cb7e039c19ccda23c6 0x4) (rN 0x6cd4e0b58b2 0x3e 124
    0xcefd3a97c3e3427c37a370025b118b2 0x0))) (wBr (wBr (rP 0x10b666bc8d6e 0x4df3 124
    0x5b222120b7d4efb17a292b1a5b2b20 0x4) (rN 0x7d4e41463e6 0x8e3d7b 125
    0x1156267bd49e7bb24f8e815abbf818ce 0x0)) (wBr (rN 0xb181428af84 0x39a3 125
    0xf7ee82abc7deef5b27b535e0c0074d3 0x25) (rP 0x6857a66d55e 0x4fbe 125
    0xa9415dab8e367e03932d73ca428387b 0x25)))) (wBr (wBr (wBr (rP 0x1a871d66d532 0x71c77b 124
    0x70ac51cc5b831da6101710f1bdfb4d5 0x25) (rN 0x8b19bb31b1f 0x38e3df3 128
    0x72b9fd33539b59712da6aa65ecc3a739 0x4)) (wBr (rN 0xcbfad801636 0xfa6 123
    0x10ec21dad815601feb2ad63f523a7b4 0x5) (rP 0x6cd4e0b58da 0x3 123
    0x10572b64db1b99ba9fa0e572fc3e962 0x25))) (wBr (wBr (rN 0x10b6628fb136 0x1c71fdf3 123
    0x75085b9865b91b07a0e3d423d53d038 0x25) (rP 0x7d4e4146435 0x13e 126
    0x1dc4a0184e428ba4f966ca5f3b4600e 0x4)) (wBr (rP 0xb181428b021 0x38e3 125
    0xf0d734328d99a7ed9831756e4c327f6 0x25) (rN 0x6857a66d54a 0x26 125
    0x571a2fe515d97f1b13daaab80c59f8 0x5))))),
    (wBr (wBr (wBr (wBr (wBr (rP 0x1665156602e45 0x71c7a6 124 0x1ac1e8ecd196e67fd7307d0f5d41adb
    0x4) (rP 0x48d163204fc 0x38f47bb 126 0x3563bfdeb7acf6b26193d47b86f819bf 0x4)) (wBr (rP
    0x6b136328751 0x71c7f3 126 0x2abf4c3c4837e95edd48e242fe7a4dbf 0x0) (rN 0x383829e9997
    0xe38e7d7b 124 0x193b0077e2c4dc6ffc8e9abee2cd7df 0x25))) (wBr (wBr (rP 0x8e01557ccc2 0xd3b
    126 0x9c7718eea722a4a05e44da7aedd6e5d 0x0) (rN 0x40bd3bc227b 0xe3d1e 123
    0x1201fe74ef32f9633b2a80eb4a0648d 0x25)) (wBr (rN 0x5b7eba1669b 0x33 123
    0x625fae3815bc08727bb52e83cdf3c85 0x5) (rP 0x35ce3ab1633 0x13e9f3 123
    0x10a5f5b307de72a89bef9e08c5327c6 0x5)))) (wBr (wBr (wBr (rP 0xae759c4f3c9 0x0 126
    0xdb3a2e7aecf1e346ea7370110ab1da5 0x0) (rN 0x454ad531d71 0x38e3d7b 125
    0x1a768dab2da1de33d586f99e6c7aea9 0x0)) (wBr (rN 0x641cab2dbf5 0x71c73b 126
    0x1a916bdcec7b5a4eaa2e5d55c01776c9 0x4) (rP 0x37961d6c416 0xd33 125
    0x17c8e9a9e2aa006b08546dabb84edc0e 0x25))) (wBr (wBr (rN 0x80a6d6073a7 0x1c71fd33 126
    0x324eb7c7e5970fa6910187b69b96db2c 0x4) (rP 0x3f9247392dd 0x4d33 125
    0x1bdf8a6f4de7b508ec58c84579694dc3 0x5)) (wBr (rP 0x59360d4bf6c 0x9a6 126
    0xe48eb80c906ce7b05a6001654eb16ff 0x4) (rN 0x358207a7250 0x38e3 123
    0x2961cf38dfb44d431da8a87a2b324fe 0x25))))) (wBr (wBr (wBr (wBr (rP 0xfd32e6a96f2 0x69f3 125
    0x761415ee37a1ded2f16749894fe60f3 0x5) (rN 0x48d15ef3c8d 0x3eb3b 121
    0x8af680ad56233a3306886895275331 0x0)) (wBr (rN 0x6b135acf576 0x4d7b 123
    0x774bbf455306d6a910df93c31ee10fc 0x0) (rP 0x383829e999c 0xf47a3 125
    0xfbeb3477d59713ff63b2347ee00dc98 0x5))) (wBr (wBr (rN 0x8e0144ca63e 0x4d3e 125
    0x8386081a7cfe3622117e28f1e5bdfcd 0x5) (rP 0x40bd3bc2285 0x17b 122
    0x3724379031b3881eaca65e6a6293b7f 0x5)) (wBr (rP 0x5b7eba166af 0x6b3b 119
    0x459c843b28f376b4ef3b8947a538e6 0x4) (rN 0x35ce3ab1632 0x13e 124
    0xdc44be753514d37e711e69dd00cbf32 0x0)))) (wBr (wBr (wBr (rN 0xae757aea033 0x33 126
    0x2abe79ed69e0c57f46f683d996a3d9f8 0x0) (rP 0x454ad531d85 0x1bb 125
    0xbd0ac6ece7d67df5ec59254da828846 0x5)) (wBr (rP 0x641cab2dc1c 0x38e3df3 126
    0x96d616d5c75f0a387fb0156a343793b 0x0) (rN 0x37961d6c414 0x0 126
    0x18dc03f561db73997776d1c544698fcb 0x4))) (wBr (wBr (rP 0x80a6d6073f5 0xfa3 124
    0x269eb0b0a1a2e998875cce842e752f6 0x0) (rN 0x3f9247392d8 0x71fd1e 126
    0x1b4bec219eac4f4416b419a1dd4ab1e6 0x4)) (wBr (rN 0x59360d4bf62 0x4df3 125
    0x125bc188fbdb6102c0a3dac90d8c3923 0x25) (rP 0x358207a7250 0x0 123
    0x327fe83cce8f3b55d1a501371e78c13 0x5)))))),
    (wBr (wBr (wBr (wBr (wBr (wBr (rP 0x16dcae859b84e 0x4fa3 124
    0xb919d78d2b4289d5384bc870469b463 0x0) (rP 0x28366618e34 0x13e 124
    0xa978f50f2b4bef3e59a1614af0e1b51 0x0)) (wBr (rP 0x39fd0d4757e 0x13e 124
    0x54dfa7d120dbc0ed8367d51e5721d35 0x0) (rN 0x1f7949a1d0a 0x38e3 124
    0x651050953126a4a2ef750b49d86cb90 0x0))) (wBr (wBr (rP 0x4c606c4e30b 0x38fe8f3 125
    0x120318a781df90cb7af25ba930b38ac2 0x5) (rN 0x23cde780c96 0x9be 125
    0xf557ffa318829d6ef4f7fc5e7081910 0x5)) (wBr (rN 0x3176be27e27 0x69f3 126
    0x32b059fabaddac635b57c122d19046e4 0x4) (rP 0x1e3bd1c2de9 0x1c71fdf3 126
    0xc2c45fe59b816c2fec09941fb6c03ba 0x4)))) (wBr (wBr (wBr (rP 0x5e382b97f22 0xe38fe 123
    0x1fcbff8ec126180a0f58f4e17e6843f 0x5) (rN 0x26273b97793 0x3d1e 124
    0xbab253dfaec9c63379ed5c652360ed8 0x4)) (wBr (rN 0x35ea3f2d8f6 0x4d33 124
    0x308994247cd50959100d44b8db94ab7 0x4) (rP 0x1f22b5e0eb5 0x38fe8fb 126
    0x24de4dcbf03453b6d168990207190698 0x4))) (wBr (wBr (rN 0x4486b7f737c 0x27d3e 126
    0x34f1b4860ec94da138d7b59511d231d 0x0) (rP 0x232d828f229 0x4d7b 120
    0xab51c1dd6361193d57fcd08ac697ed 0x5)) (wBr (rP 0x303cac017a9 0x27d7b 124
    0xf18cdf7e6b1cc86495ae08002b2dde4 0x5) (rN 0x1e1482b0d2d 0xe38e3 124
    0x14070bc9926044d0b7dd5b2387152ad 0x0))))) (wBr (wBr (wBr (wBr (rP 0x6e8b84dbb32 0x9f3 124
    0x47a0d8d53ca226b2ea95d587994a594 0x0) (rN 0x2753707c8c6 0x4d7b 126
    0x6eaded102e453050bbf3789983d0ebf 0x25)) (wBr (rN 0x3838a431569 0x26b3b 124
    0xab24abb8664908c4f13af10e1f09867 0x5) (rP 0x1f64413422a 0x38e3 124
    0xb1a2b41e1b57dead28f346cbfc6f77 0x4))) (wBr (wBr (rN 0x48e2e8a6945 0x1c71fdf3 120
    0xf6d9618fc110c0628b9ea72613388a 0x0) (rP 0x23a4e9c68d5 0x6 120
    0xc4abbe93a536d250ca67fdaecc95f2 0x0)) (wBr (rP 0x31254e91d9a 0x6b3b 123
    0x1a971ef91ae0a311e5fc79b7f499c7a 0x4) (rN 0x1e3618b839c 0xd3b 123
    0x3fa05f795bf613f0e5159012f0f70d5 0x5)))) (wBr (wBr (wBr (rN 0x57872e3a731 0x1c71fdf3 126
    0x736e634505de79736228bf7c98de866 0x4) (rP 0x25dbb203a5a 0x27d3e 125
    0xb0de7b300e8f9320e0a7f61a53e0633 0x25)) (wBr (rP 0x355415541af 0xfa6 124
    0x2a3193d537fdd355db4a3997b33f2dc 0x0) (rN 0x1f18a5c6368 0x71e 124
    0xffb1d7a6d27bfca12e0a59fa8e16cca 0x4))) (wBr (wBr (rP 0x43611674fec 0x71c73b 124
    0xdf2f383ec2fdecb9eb1521ba7bad042 0x0) (rN 0x231a20a666a 0x13e9f3 128
    0xf0e6cbfc5786b5143598578476d82ea 0x0)) (wBr (rN 0x3016494ae98 0x38e3d33 123
    0x4e35003faaf9677a9ae6196a7335fc0 0x5) (rP 0x1e111c8b494 0x3e 126
    0x3f3209bb0f2a760001e5b5f4f0af2be3 0x4)))))) (wBr (wBr (wBr (wBr (wBr (rP 0x95f0bbcf021 0x23
    124 0xc664fa1266f698a6f296fc9647a5577 0x0) (rN 0x2836650dc2c 0xe38fb 123
    0x326a2b662979f498a8b5c9946c68a0f 0x25)) (wBr (rN 0x39fd0b3115a 0x7d3b 126
    0x3abd12ee51764780b36cb93edd71bc16 0x0) (rP 0x1f7949a1d0a 0x38f47a3 124
    0xeb6815d3ab823ba442bcab31e9a7566 0x0))) (wBr (wBr (rN 0x4c606821a92 0xd3b 125
    0xd1e10c57318dd6b1974d851ea69de4f 0x5) (rP 0x23cde780c97 0x9be 125
    0x652ecb8a15259f41b0f9a7573248719 0x5)) (wBr (rP 0x3176be27e29 0x4d3b 125
    0x12394493dcc5bf6ae384d058f6901858 0x25) (rN 0x1e3bd1c2de9 0x71fd7b 125
    0x19382fe6a5c56871696ae591f4e4c9a 0x0)))) (wBr (wBr (wBr (rN 0x5e38233edb3 0x1c71fdf3 126
    0xbb6c42506766072c06de863a869f204 0x0) (rP 0x26273b97795 0x3d1e 124
    0x9b706c4a63ab79ecc639375fbca4d5c 0x4)) (wBr (rP 0x35ea3f2d8fb 0xd33 124
    0x80e446dc64f06d3f726705392f2fcba 0x0) (rN 0x1f22b5e0eb5 0xe38e3 125
    0x8c0236794e5b3ea3a10b131cc560b43 0x25))) (wBr (wBr (rP 0x4486b7f7386 0x3 125
    0x1aae4c7ce580bb8fd008903bafedc535 0x25) (rN 0x232d828f229 0x26 121
    0x1b7e963510b3feabc9886c6bb838ad5 0x25)) (wBr (rN 0x303cac017a8 0x4fbe 125
    0x916020f6da6aec490c85560a5968754 0x25) (rP 0x1e1482b0d2d 0x1c71e9f3 124
    0xd8fc5571fb70d366694dd24250b8d9e 0x0))))) (wBr (wBr (wBr (wBr (rN 0x6e8b7429749 0x1be 124
    0x2b994c18b43f93f2fedeab28f1ed683 0x0) (rP 0x2753707c8cb 0x4d7b 126
    0x3f5c2f06647b3f74283289d022ded5d8 0x25)) (wBr (rP 0x3838a431573 0x11c7a3 125
    0x8a6f494c4ccb675f5d5a79bb345995c 0x25) (rN 0x1f644134229 0xfa3 123
    0x1acdc48407bce7ec6698dae77b141de 0x5))) (wBr (wBr (rP 0x48e2e8a6958 0x8e3d7b 119
    0xa717ebf88cf0a2bb5d3ee475df6d9 0x4) (rN 0x23a4e9c68d5 0x33 119
    0x27d499badff3298525b652e4beea91 0x25)) (wBr (rN 0x31254e91d99 0x4df3 123
    0x19c7a4c9b79c4be72b9ee1a94d1c277 0x25) (rP 0x1e3618b839c 0x4fbb 123
    0xf096abce785678a6a3afd9e59b3bdb 0x25)))) (wBr (wBr (wBr (rP 0x57872e3a759 0xe3d7b 125
    0xf5e81d22099e7c057cf35ef3dc2b68e 0x4) (rN 0x25dbb203a58 0x27d7b 124
    0x170dca7eeb488b1dfa447ab6168a060 0x25)) (wBr (rN 0x355415541ac 0x1c71cdf3 123
    0x46ca50b421544db0e08692d38521d47 0x5) (rP 0x1f18a5c6368 0x7d33 124
    0xe5edeaa322c8b1933e4b3fdbe863b25 0x4))) (wBr (wBr (rN 0x43611674fe7 0x4d3b 124
    0x9966eb3eb5fc561465a099811aa2f96 0x0) (rP 0x231a20a666a 0x38e3d33 128
    0xe19adb54c5cc2c19e760c5ce4bed1d46 0x0)) (wBr (rP 0x3016494ae98 0xd3e 124
    0x5a90d0a9d975e1a741ef97193b68d54 0x0) (rN 0x1e111c8b494 0x133 125
    0x397287a88436f9db6d6a728c0dfbf44 0x25)))))))]

section CertifiedRegimes

theorem regData_47487_7_ok : checkTwoGearRegime regData_47487_7 = true := by decide +kernel

end CertifiedRegimes

end QuantumComputationSpecs.Algorithms.P450GroundEnergy.Solution.TwoGearQPEPhase5

namespace QuantumComputationSpecs.Algorithms.P450GroundEnergy.Solution.TailShiftWindow46847
open QuantumComputation.Specs QuantumComputation.Specs.P450
open TwoGearQPEPhase5
open SevenGearBondDefer

/-- Certified `0`-ancilla `ThreeGearBondDeferSpec 47487 10 7 0` (`tWin = 142248`). -/
noncomputable def threeGearWin_47487_10_7 : ThreeGearBondDeferSpec 47487 10 7 0 :=
  mkThreeGearBondDeferSpec_zeroAnc regData_47487_7 10 regData_47487_7_ok

@[simp] theorem threeGearWin_47487_10_7_tWin :
    threeGearWin_47487_10_7.base.tWin = 142248 := rfl

@[simp] theorem threeGearWin_47487_10_7_δWin :
    threeGearWin_47487_10_7.base.δWin = 5 / 10 ^ 9 := rfl

/-- Computable `ThreeGearWindowCirc 10 7 0` for `(47487, 10, 7)`. -/
def threeGearWinCirc_47487_10_7 : ThreeGearWindowCirc 10 7 0 :=
  mkThreeGearWindowCirc_zeroAnc regData_47487_7 10

@[simp] theorem threeGearWin_47487_10_7_toCirc :
    threeGearWin_47487_10_7.toCirc = threeGearWinCirc_47487_10_7 := rfl

@[simp] theorem threeGearWin_47487_10_7_cWinC :
    threeGearWin_47487_10_7.cWinC = cWinPrefixAt regData_47487_7 10 := rfl

end QuantumComputationSpecs.Algorithms.P450GroundEnergy.Solution.TailShiftWindow46847
end
