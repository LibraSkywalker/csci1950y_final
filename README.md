### Introduction

In this project, we have developed the **Dolev-Yao attacker model**, which is a formal model used to prove properties of interactive cryptographic protocols.

The development is base on the resource from [UCSD](https://cseweb.ucsd.edu/classes/sp05/cse208/lec-dolevyao.html) :

We are going to determine whether the different authentication protocols have potential vulnerability with the Dolev-Yao attacker model.

In our model, it will have three users (sender, receiver, attacker). The sender will send different messages to the receiver. The receiver will get the message from the sender and send back the message. The attacker will try to intercept the message from the sender or receiver. What we try to prove is that attacker could intercept the message and decode it.

For the attacker, we made it could intercept all message from both sides(sender and receiver), it also could store all the messages that it intercepts, it also could send the intercepted message and its own constructed message. And the Attacker will be valid in the system and not been exposed.

For the sender, it will have a public key and private key to encode its message so that it could protect its message.
For the receiver, it will have also have a public key and private key to decode the sender’s message and encode its response.

For the message, it will include the composed message and encrypted message. The composed message will have a signature.

Then we import the **NSPK** protocol and try to use our Dolev-Yao attacker model to attack it and see if there is any leak. For the NSPK protocol, it will have three states:

A &#8594; B: K<sub>B</sub>{N<sub>A</sub>, A}

B &#8594; A: K<sub>A</sub>{N<sub>B</sub>, B}

A &#8594; B: K<sub>B</sub>{N<sub>B</sub>}

For this protocol, N is the message, and K will be the public key. We are trying to see if the attacker could get the N.
