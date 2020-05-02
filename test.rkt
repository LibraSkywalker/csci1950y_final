#lang forge
-- Role
sig User {}

one sig Stranger extends User{}

one sig Attacker extends User{}

-- Message

sig Message {}

sig Key extends Message{
	paired: one Key,
	belongs: one User
}

pred initProtocol{ -- some common knowledge
	-- private key encryption

        
        all user : User | {
            one key : Key | {
                key.belongs = user
            }
        }
}

run  {initProtocol}  for exactly 5 User, exactly 5 Key