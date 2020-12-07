# Experiments

This directory contains experiments for testing validity and assessing the performance of our toolchain.

## Usage

We included a script for running all experiments sequentially, or just a specific subset by passing a sequence of identifiers.

```
./run [<id> ...]
```

Hint: Bash's *brace expansion* can be used to generate sequences of experiment identifiers.
For example, use the following command to run all litmus tests.

```
./run {1..133}
```

## Benchmark Array

| ID  | Directory       | Command                               |
| --- | --------------- | ------------------------------------- |
| 1   | litmus/intel/1  | run.sh btormc btor2                   |
| 2   | litmus/intel/1  | run.sh boolector functional           |
| 3   | litmus/intel/1  | run.sh boolector relational           |
| 4   | litmus/intel/1  | run.sh cvc4 functional                |
| 5   | litmus/intel/1  | run.sh cvc4 relational                |
| 6   | litmus/intel/1  | run.sh z3 functional                  |
| 7   | litmus/intel/1  | run.sh z3 relational                  |
|     |                 |                                       |
| 8   | litmus/intel/2  | run.sh btormc btor2                   |
| 9   | litmus/intel/2  | run.sh boolector functional           |
| 10  | litmus/intel/2  | run.sh boolector relational           |
| 11  | litmus/intel/2  | run.sh cvc4 functional                |
| 12  | litmus/intel/2  | run.sh cvc4 relational                |
| 13  | litmus/intel/2  | run.sh z3 functional                  |
| 14  | litmus/intel/2  | run.sh z3 relational                  |
|     |                 |                                       |
| 15  | litmus/intel/3  | run.sh btormc btor2                   |
| 16  | litmus/intel/3  | run.sh boolector functional           |
| 17  | litmus/intel/3  | run.sh boolector relational           |
| 18  | litmus/intel/3  | run.sh cvc4 functional                |
| 19  | litmus/intel/3  | run.sh cvc4 relational                |
| 20  | litmus/intel/3  | run.sh z3 functional                  |
| 21  | litmus/intel/3  | run.sh z3 relational                  |
|     |                 |                                       |
| 22  | litmus/intel/4  | run.sh btormc btor2                   |
| 23  | litmus/intel/4  | run.sh boolector functional           |
| 24  | litmus/intel/4  | run.sh boolector relational           |
| 25  | litmus/intel/4  | run.sh cvc4 functional                |
| 26  | litmus/intel/4  | run.sh cvc4 relational                |
| 27  | litmus/intel/4  | run.sh z3 functional                  |
| 28  | litmus/intel/4  | run.sh z3 relational                  |
|     |                 |                                       |
| 29  | litmus/intel/5  | run.sh btormc btor2                   |
| 30  | litmus/intel/5  | run.sh boolector functional           |
| 31  | litmus/intel/5  | run.sh boolector relational           |
| 32  | litmus/intel/5  | run.sh cvc4 functional                |
| 33  | litmus/intel/5  | run.sh cvc4 relational                |
| 34  | litmus/intel/5  | run.sh z3 functional                  |
| 35  | litmus/intel/5  | run.sh z3 relational                  |
|     |                 |                                       |
| 36  | litmus/intel/6  | run.sh btormc btor2                   |
| 37  | litmus/intel/6  | run.sh boolector functional           |
| 38  | litmus/intel/6  | run.sh boolector relational           |
| 39  | litmus/intel/6  | run.sh cvc4 functional                |
| 40  | litmus/intel/6  | run.sh cvc4 relational                |
| 41  | litmus/intel/6  | run.sh z3 functional                  |
| 42  | litmus/intel/6  | run.sh z3 relational                  |
|     |                 |                                       |
| 43  | litmus/intel/7  | run.sh btormc btor2                   |
| 44  | litmus/intel/7  | run.sh boolector functional           |
| 45  | litmus/intel/7  | run.sh boolector relational           |
| 46  | litmus/intel/7  | run.sh cvc4 functional                |
| 47  | litmus/intel/7  | run.sh cvc4 relational                |
| 48  | litmus/intel/7  | run.sh z3 functional                  |
| 49  | litmus/intel/7  | run.sh z3 relational                  |
|     |                 |                                       |
| 50  | litmus/intel/8  | run.sh btormc btor2                   |
| 51  | litmus/intel/8  | run.sh boolector functional           |
| 52  | litmus/intel/8  | run.sh boolector relational           |
| 53  | litmus/intel/8  | run.sh cvc4 functional                |
| 54  | litmus/intel/8  | run.sh cvc4 relational                |
| 55  | litmus/intel/8  | run.sh z3 functional                  |
| 56  | litmus/intel/8  | run.sh z3 relational                  |
|     |                 |                                       |
| 57  | litmus/intel/9  | run.sh btormc btor2                   |
| 58  | litmus/intel/9  | run.sh boolector functional           |
| 59  | litmus/intel/9  | run.sh boolector relational           |
| 60  | litmus/intel/9  | run.sh cvc4 functional                |
| 61  | litmus/intel/9  | run.sh cvc4 relational                |
| 62  | litmus/intel/9  | run.sh z3 functional                  |
| 63  | litmus/intel/9  | run.sh z3 relational                  |
|     |                 |                                       |
| 64  | litmus/intel/10 | run.sh btormc btor2                   |
| 65  | litmus/intel/10 | run.sh boolector functional           |
| 66  | litmus/intel/10 | run.sh boolector relational           |
| 67  | litmus/intel/10 | run.sh cvc4 functional                |
| 68  | litmus/intel/10 | run.sh cvc4 relational                |
| 69  | litmus/intel/10 | run.sh z3 functional                  |
| 70  | litmus/intel/10 | run.sh z3 relational                  |
|     |                 |                                       |
| 71  | litmus/amd/1    | run.sh btormc btor2                   |
| 72  | litmus/amd/1    | run.sh boolector functional           |
| 73  | litmus/amd/1    | run.sh boolector relational           |
| 74  | litmus/amd/1    | run.sh cvc4 functional                |
| 75  | litmus/amd/1    | run.sh cvc4 relational                |
| 76  | litmus/amd/1    | run.sh z3 functional                  |
| 77  | litmus/amd/1    | run.sh z3 relational                  |
|     |                 |                                       |
| 78  | litmus/amd/2    | run.sh btormc btor2                   |
| 79  | litmus/amd/2    | run.sh boolector functional           |
| 80  | litmus/amd/2    | run.sh boolector relational           |
| 81  | litmus/amd/2    | run.sh cvc4 functional                |
| 82  | litmus/amd/2    | run.sh cvc4 relational                |
| 83  | litmus/amd/2    | run.sh z3 functional                  |
| 84  | litmus/amd/2    | run.sh z3 relational                  |
|     |                 |                                       |
| 85  | litmus/amd/3    | run.sh btormc btor2                   |
| 86  | litmus/amd/3    | run.sh boolector functional           |
| 87  | litmus/amd/3    | run.sh boolector relational           |
| 88  | litmus/amd/3    | run.sh cvc4 functional                |
| 89  | litmus/amd/3    | run.sh cvc4 relational                |
| 90  | litmus/amd/3    | run.sh z3 functional                  |
| 91  | litmus/amd/3    | run.sh z3 relational                  |
|     |                 |                                       |
| 92  | litmus/amd/4    | run.sh btormc btor2                   |
| 93  | litmus/amd/4    | run.sh boolector functional           |
| 94  | litmus/amd/4    | run.sh boolector relational           |
| 95  | litmus/amd/4    | run.sh cvc4 functional                |
| 96  | litmus/amd/4    | run.sh cvc4 relational                |
| 97  | litmus/amd/4    | run.sh z3 functional                  |
| 98  | litmus/amd/4    | run.sh z3 relational                  |
|     |                 |                                       |
| 99  | litmus/amd/5    | run.sh btormc btor2                   |
| 100 | litmus/amd/5    | run.sh boolector functional           |
| 101 | litmus/amd/5    | run.sh boolector relational           |
| 102 | litmus/amd/5    | run.sh cvc4 functional                |
| 103 | litmus/amd/5    | run.sh cvc4 relational                |
| 104 | litmus/amd/5    | run.sh z3 functional                  |
| 105 | litmus/amd/5    | run.sh z3 relational                  |
|     |                 |                                       |
| 106 | litmus/amd/6    | run.sh btormc btor2                   |
| 107 | litmus/amd/6    | run.sh boolector functional           |
| 108 | litmus/amd/6    | run.sh boolector relational           |
| 109 | litmus/amd/6    | run.sh cvc4 functional                |
| 110 | litmus/amd/6    | run.sh cvc4 relational                |
| 111 | litmus/amd/6    | run.sh z3 functional                  |
| 112 | litmus/amd/6    | run.sh z3 relational                  |
|     |                 |                                       |
| 113 | litmus/amd/7    | run.sh btormc btor2                   |
| 114 | litmus/amd/7    | run.sh boolector functional           |
| 115 | litmus/amd/7    | run.sh boolector relational           |
| 116 | litmus/amd/7    | run.sh cvc4 functional                |
| 117 | litmus/amd/7    | run.sh cvc4 relational                |
| 118 | litmus/amd/7    | run.sh z3 functional                  |
| 119 | litmus/amd/7    | run.sh z3 relational                  |
|     |                 |                                       |
| 120 | litmus/amd/8    | run.sh btormc btor2                   |
| 121 | litmus/amd/8    | run.sh boolector functional           |
| 122 | litmus/amd/8    | run.sh boolector relational           |
| 123 | litmus/amd/8    | run.sh cvc4 functional                |
| 124 | litmus/amd/8    | run.sh cvc4 relational                |
| 125 | litmus/amd/8    | run.sh z3 functional                  |
| 126 | litmus/amd/8    | run.sh z3 relational                  |
|     |                 |                                       |
| 127 | litmus/amd/9    | run.sh btormc btor2                   |
| 128 | litmus/amd/9    | run.sh boolector functional           |
| 129 | litmus/amd/9    | run.sh boolector relational           |
| 130 | litmus/amd/9    | run.sh cvc4 functional                |
| 131 | litmus/amd/9    | run.sh cvc4 relational                |
| 132 | litmus/amd/9    | run.sh z3 functional                  |
| 133 | litmus/amd/9    | run.sh z3 relational                  |
|     |                 |                                       |
| 134 | count_stat      | run.sh buggy 2 2 btormc btor2         |
| 135 | count_stat      | run.sh buggy 2 2 boolector functional |
| 136 | count_stat      | run.sh buggy 2 2 boolector relational |
| 137 | count_stat      | run.sh buggy 2 2 cvc4 functional      |
| 138 | count_stat      | run.sh buggy 2 2 cvc4 relational      |
| 139 | count_stat      | run.sh buggy 2 2 z3 functional        |
| 140 | count_stat      | run.sh buggy 2 2 z3 relational        |
|     |                 |                                       |
| 141 | count_stat      | run.sh buggy 2 3 btormc btor2         |
| 142 | count_stat      | run.sh buggy 2 3 boolector functional |
| 143 | count_stat      | run.sh buggy 2 3 boolector relational |
| 144 | count_stat      | run.sh buggy 2 3 cvc4 functional      |
| 145 | count_stat      | run.sh buggy 2 3 cvc4 relational      |
| 146 | count_stat      | run.sh buggy 2 3 z3 functional        |
| 147 | count_stat      | run.sh buggy 2 3 z3 relational        |
|     |                 |                                       |
| 148 | count_stat      | run.sh buggy 2 4 btormc btor2         |
| 149 | count_stat      | run.sh buggy 2 4 boolector functional |
| 150 | count_stat      | run.sh buggy 2 4 boolector relational |
| 151 | count_stat      | run.sh buggy 2 4 cvc4 functional      |
| 152 | count_stat      | run.sh buggy 2 4 cvc4 relational      |
| 153 | count_stat      | run.sh buggy 2 4 z3 functional        |
| 154 | count_stat      | run.sh buggy 2 4 z3 relational        |
|     |                 |                                       |
| 155 | count_stat      | run.sh buggy 3 2 btormc btor2         |
| 156 | count_stat      | run.sh buggy 3 2 boolector functional |
| 157 | count_stat      | run.sh buggy 3 2 boolector relational |
| 158 | count_stat      | run.sh buggy 3 2 cvc4 functional      |
| 159 | count_stat      | run.sh buggy 3 2 cvc4 relational      |
| 160 | count_stat      | run.sh buggy 3 2 z3 functional        |
| 161 | count_stat      | run.sh buggy 3 2 z3 relational        |
|     |                 |                                       |
| 162 | count_stat      | run.sh buggy 3 3 btormc btor2         |
| 163 | count_stat      | run.sh buggy 3 3 boolector functional |
| 164 | count_stat      | run.sh buggy 3 3 boolector relational |
| 165 | count_stat      | run.sh buggy 3 3 cvc4 functional      |
| 166 | count_stat      | run.sh buggy 3 3 cvc4 relational      |
| 167 | count_stat      | run.sh buggy 3 3 z3 functional        |
| 168 | count_stat      | run.sh buggy 3 3 z3 relational        |
|     |                 |                                       |
| 169 | count_stat      | run.sh buggy 3 4 btormc btor2         |
| 170 | count_stat      | run.sh buggy 3 4 boolector functional |
| 171 | count_stat      | run.sh buggy 3 4 boolector relational |
| 172 | count_stat      | run.sh buggy 3 4 cvc4 functional      |
| 173 | count_stat      | run.sh buggy 3 4 cvc4 relational      |
| 174 | count_stat      | run.sh buggy 3 4 z3 functional        |
| 175 | count_stat      | run.sh buggy 3 4 z3 relational        |
|     |                 |                                       |
| 176 | count_stat      | run.sh buggy 4 2 btormc btor2         |
| 177 | count_stat      | run.sh buggy 4 2 boolector functional |
| 178 | count_stat      | run.sh buggy 4 2 boolector relational |
| 179 | count_stat      | run.sh buggy 4 2 cvc4 functional      |
| 180 | count_stat      | run.sh buggy 4 2 cvc4 relational      |
| 181 | count_stat      | run.sh buggy 4 2 z3 functional        |
| 182 | count_stat      | run.sh buggy 4 2 z3 relational        |
|     |                 |                                       |
| 183 | count_stat      | run.sh buggy 4 3 btormc btor2         |
| 184 | count_stat      | run.sh buggy 4 3 boolector functional |
| 185 | count_stat      | run.sh buggy 4 3 boolector relational |
| 186 | count_stat      | run.sh buggy 4 3 cvc4 functional      |
| 187 | count_stat      | run.sh buggy 4 3 cvc4 relational      |
| 188 | count_stat      | run.sh buggy 4 3 z3 functional        |
| 189 | count_stat      | run.sh buggy 4 3 z3 relational        |
|     |                 |                                       |
| 190 | count_stat      | run.sh buggy 4 4 btormc btor2         |
| 191 | count_stat      | run.sh buggy 4 4 boolector functional |
| 192 | count_stat      | run.sh buggy 4 4 boolector relational |
| 193 | count_stat      | run.sh buggy 4 4 cvc4 functional      |
| 194 | count_stat      | run.sh buggy 4 4 cvc4 relational      |
| 195 | count_stat      | run.sh buggy 4 4 z3 functional        |
| 196 | count_stat      | run.sh buggy 4 4 z3 relational        |
|     |                 |                                       |
| 197 | count_stat      | run.sh cas 2 2 btormc btor2           |
| 198 | count_stat      | run.sh cas 2 2 boolector functional   |
| 199 | count_stat      | run.sh cas 2 2 boolector relational   |
| 200 | count_stat      | run.sh cas 2 2 cvc4 functional        |
| 201 | count_stat      | run.sh cas 2 2 cvc4 relational        |
| 202 | count_stat      | run.sh cas 2 2 z3 functional          |
| 203 | count_stat      | run.sh cas 2 2 z3 relational          |
|     |                 |                                       |
| 204 | count_stat      | run.sh cas 2 3 btormc btor2           |
| 205 | count_stat      | run.sh cas 2 3 boolector functional   |
| 206 | count_stat      | run.sh cas 2 3 boolector relational   |
| 207 | count_stat      | run.sh cas 2 3 cvc4 functional        |
| 208 | count_stat      | run.sh cas 2 3 cvc4 relational        |
| 209 | count_stat      | run.sh cas 2 3 z3 functional          |
| 210 | count_stat      | run.sh cas 2 3 z3 relational          |
|     |                 |                                       |
| 211 | count_stat      | run.sh cas 2 4 btormc btor2           |
| 212 | count_stat      | run.sh cas 2 4 boolector functional   |
| 213 | count_stat      | run.sh cas 2 4 boolector relational   |
| 214 | count_stat      | run.sh cas 2 4 cvc4 functional        |
| 215 | count_stat      | run.sh cas 2 4 cvc4 relational        |
| 216 | count_stat      | run.sh cas 2 4 z3 functional          |
| 217 | count_stat      | run.sh cas 2 4 z3 relational          |
|     |                 |                                       |
| 218 | count_stat      | run.sh cas 3 2 btormc btor2           |
| 219 | count_stat      | run.sh cas 3 2 boolector functional   |
| 220 | count_stat      | run.sh cas 3 2 boolector relational   |
| 221 | count_stat      | run.sh cas 3 2 cvc4 functional        |
| 222 | count_stat      | run.sh cas 3 2 cvc4 relational        |
| 223 | count_stat      | run.sh cas 3 2 z3 functional          |
| 224 | count_stat      | run.sh cas 3 2 z3 relational          |
|     |                 |                                       |
| 225 | count_stat      | run.sh cas 3 3 btormc btor2           |
| 226 | count_stat      | run.sh cas 3 3 boolector functional   |
| 227 | count_stat      | run.sh cas 3 3 boolector relational   |
| 228 | count_stat      | run.sh cas 3 3 cvc4 functional        |
| 229 | count_stat      | run.sh cas 3 3 cvc4 relational        |
| 230 | count_stat      | run.sh cas 3 3 z3 functional          |
| 231 | count_stat      | run.sh cas 3 3 z3 relational          |
|     |                 |                                       |
| 232 | count_stat      | run.sh cas 3 4 btormc btor2           |
| 233 | count_stat      | run.sh cas 3 4 boolector functional   |
| 234 | count_stat      | run.sh cas 3 4 boolector relational   |
| 235 | count_stat      | run.sh cas 3 4 cvc4 functional        |
| 236 | count_stat      | run.sh cas 3 4 cvc4 relational        |
| 237 | count_stat      | run.sh cas 3 4 z3 functional          |
| 238 | count_stat      | run.sh cas 3 4 z3 relational          |
|     |                 |                                       |
| 239 | count_stat      | run.sh cas 4 2 btormc btor2           |
| 240 | count_stat      | run.sh cas 4 2 boolector functional   |
| 241 | count_stat      | run.sh cas 4 2 boolector relational   |
| 242 | count_stat      | run.sh cas 4 2 cvc4 functional        |
| 243 | count_stat      | run.sh cas 4 2 cvc4 relational        |
| 244 | count_stat      | run.sh cas 4 2 z3 functional          |
| 245 | count_stat      | run.sh cas 4 2 z3 relational          |
|     |                 |                                       |
| 246 | count_stat      | run.sh cas 4 3 btormc btor2           |
| 247 | count_stat      | run.sh cas 4 3 boolector functional   |
| 248 | count_stat      | run.sh cas 4 3 boolector relational   |
| 249 | count_stat      | run.sh cas 4 3 cvc4 functional        |
| 250 | count_stat      | run.sh cas 4 3 cvc4 relational        |
| 251 | count_stat      | run.sh cas 4 3 z3 functional          |
| 252 | count_stat      | run.sh cas 4 3 z3 relational          |
|     |                 |                                       |
| 253 | count_stat      | run.sh cas 4 4 btormc btor2           |
| 254 | count_stat      | run.sh cas 4 4 boolector functional   |
| 255 | count_stat      | run.sh cas 4 4 boolector relational   |
| 256 | count_stat      | run.sh cas 4 4 cvc4 functional        |
| 257 | count_stat      | run.sh cas 4 4 cvc4 relational        |
| 258 | count_stat      | run.sh cas 4 4 z3 functional          |
| 259 | count_stat      | run.sh cas 4 4 z3 relational          |
