#lang forge
-- Message

sig Message {}

sig Key extends Message{
	paired: one Key,
	belongs: one User
}

sig ComposedMessage extends Message{
    subMessage1: one Message,
    subMessage2: one Message
}
sig EncryptedMessage extends Message{
    content: one Key->Message
}

sig RandomMessage extends Message{}

sig NetworkFlow {
    source : one User,
    destination : one User,
    msg : one Message
}

-- Role

sig User {}

one sig Stranger extends User{}

one sig Attacker extends User{}

pred composeMessage[mC: ComposedMessage, m1: Message, m2: Message]{
	mC.subMessage1 = m1
        mC.subMessage2 = m2
}

pred encryptMessage[mE: EncryptedMessage, mP: Message, encryptKey: Key]{
	mE.content = encryptKey.paired -> mP
}

pred synthesize[processedMessage: Message, rawMessage: Message]{
       let curComposed = (processedMessage & ComposedMessage) |
       let curEncrypt = (processedMessage & EncryptedMessage) | {
           curComposed.subMessage1 in processedMessage                        --  Compose
           curComposed.subMessage2 in processedMessage                        --  Compose
           curEncrypt.content in (processedMessage & Key) -> processedMessage --  Encrypt
           processedMessage = rawMessage
                        + curComposed.subMessage1                             -- Decompose
                        + curComposed.subMessage2                             -- Decompose
                        + (processedMessage & Key).(curEncrypt.content)       -- Decrypt
                        + curEncrypt                                          -- Encrypt
                        + curComposed                                         -- Compose
      }
}

-- Protocol

-- abstract protocol
sig Step{
    nextStep: one Step
}

one sig initStep extends Step{}

pred finalStep[step: Step]{
    step.nextStep = step
}

sig Status{
	-- protocol status metadata
	claimedAuth : one User->User, -- claimer, claimed
	curStep : one Step,
	
	-- last update
	sender : one User,
	receiver : one User,

        -- Messages
        inMsg : one Message,
        outMsg : one Message
}


sig StatusChange{
   linkage: set Status->Status
}


pred protocolExecution [nextStatus: Status, curStatus: Status, receivedMessages: NetworkFlow]{
    some flow: destination.(curStatus.receiver) & receivedMessages | {
       flow.msg = curStatus.inMsg
       flow.source = curStatus.sender
       curStatus.claimedAuth = nextStatus.claimedAuth
       nextStatus.curStep = curStatus.curStep.nextStep
       nextStatus.sender = curStatus.receiver
       nextStatus.receiver = curStatus.sender
       nextStatus.inMsg = curStatus.outMsg
     }
}


-- concrete protocol (NSPK)

-- Alice encrypt a random num with Bob's key, send to Bob
pred regulateStep0[step: Step, hasMessages: User->Message]{
	all status: curStep.step | {
                -- out Message Structure
                status.inMsg in RandomMessage & status.sender.hasMessages
                encryptMessage[status.outMsg, status.inMsg, belongs.(status.receiver)]
	}
        not finalStep[step]
	
}



-- Bob decrypt a random num, and append a random num afterward and encrypt with Alice's key, send to Alice

pred regulateStep1[step: Step, hasMessages: User->Message]{
	all status : curStep.step | {
             one innerMessage : ComposedMessage |
             some plaintext : RandomMessage - status.sender.hasMessages | 
             one plaintext2: RandomMessage & status.sender.hasMessages | {
                 -- in Message Structure
		encryptMessage[status.inMsg, plaintext, belongs.(status.sender)]

                -- out Message Structure
                composeMessage[innerMessage, plaintext, plaintext2]
                encryptMessage[status.outMsg, innerMessage, belongs.(status.receiver)]
             }
	}
        not finalStep[step]
}

-- Alice check if her random number is returned and reply with Bob's randon num to Bob
pred regulateStep2[step: Step, hasMessages: User->Message]{
	all status : curStep.step | {
             some innerMessage : ComposedMessage |
             some plaintext : RandomMessage & status.sender.hasMessages |
	     some plaintext2 : RandomMessage | {
		-- in Message Structure
		encryptMessage[status.inMsg, innerMessage,belongs.(status.sender)]
                --innerMessage.subMessage1 = plaintext
		composeMessage[innerMessage, plaintext, plaintext2]
			
		-- out Message Structure
		encryptMessage[status.outMsg, plaintext2, belongs.(status.receiver)]	
	
	     }
	}
        not finalStep[step]
}

-- Alice check if his random number is returned
pred regulateStep3[step: Step, hasMessages: User->Message]{
	all status : curStep.step | {
		one plaintext : RandomMessage & status.sender.hasMessages | {
			-- in Message Structure
			encryptMessage[status.inMsg, plaintext, belongs.(status.sender)]
		}
		
	
	}
        finalStep[step]	 -- final step
}

pred initProtocol[hasMessages: User->Message]{ -- some common knowledge
	-- private key encryption
	all key : Key | {
		key.paired = key
	}

        all user : User | {
            one key : Key | {
                key.belongs = user
            }
            one random : RandomMessage | {
                random in user.hasMessages
                random not in (User - user).hasMessages
            }
        }
	
	-- all user has this key
	all user : User | {
		Key in user.hasMessages
	}

        -- regulate steps
        regulateStep0[initStep, hasMessages]
        regulateStep1[initStep.nextStep, hasMessages]
        regulateStep2[initStep.nextStep.nextStep, hasMessages]
        regulateStep3[initStep.nextStep.nextStep.nextStep, hasMessages]
        
}

-- Attacker

pred DolevYaoAttacker[totalMessage: Message, interceptedMessages: NetworkFlow, sentMessages: NetworkFlow, rawMessage: Message]{
	interceptedMessages in sentMessages 				-- intercept
        synthesize[totalMessage, rawMessage + sentMessages.msg]	        -- overhear and synthesize
        ((Attacker.source) & sentMessages).msg in rawMessage            -- inject			
}

pred DolevProtocolIntercept[nextStatus: Status, curStatus: Status]{
	nextStatus.claimedAuth = curStatus.claimedAuth
	nextStatus.curStep = curStatus.curStep
	nextStatus.sender = curStatus.sender
	nextStatus.receiver = Attacker
}

-- Exectution

sig State {
	status 			: set Status,
	newStatus		: set Status,
	finishedStatus		: set Status,
	authAs			: set User->User->User,  	-- receiver, sender, claimed_auth
	sentMessages 		: set NetworkFlow, 	-- sender, message, receiver
	receivedMessages 	: set NetworkFlow,	-- sender, message, receiver
	interceptedMessages     : set NetworkFlow,	-- sender, message, receiver
	hasMessages 		: set User->Message
}

state[State] initState{
	no status
	no newStatus
	no finishedStatus
	authAs = User->User->Stranger
	no sentMessages
	no receivedMessages
	no interceptedMessages
        initProtocol[hasMessages]
}

transition[State] processState{
    	--no status'
	--no newStatus'
	--no finishedStatus'
	--authAs' = User->User->Stranger
	--no sentMessages'
        --no receivedMessages'
	--no interceptedMessages'
        --no hasMessages'

        -- check finished Status
  

        all nextStatus : finishedStatus' | {
             finalStep[nextStatus.curStep]
             nextStatus in status
        }

	-- add newStatus
        all nextStatus: newStatus' | {
            nextStatus.curStep = initStep 	-- only initStep allowed in new status	
        }				
	
	all initStatus : newStatus' - sender.Attacker | {
                initStatus.sender = initStatus.claimedAuth.User             -- claimed for themselves
		initStatus.claimedAuth.User = User.(initStatus.claimedAuth) -- user are honest
		no initStatus.sender & initStatus.receiver 		    -- no need for self auth
		initStatus.receiver->initStatus.sender in authAs'.Stranger  -- no need for authed user8
                
	}
	newStatus' in status'
	
	-- constraints for status'
	all nextStatus: status' - newStatus' | {
              
              no status & nextStatus => {some curStatus : status | {
                   protocolExecution[nextStatus, curStatus, receivedMessages]
              }} 
	}

        -- constraints for sentMessages'
        all nextStatus: status'  | some flow : sentMessages' | {
            nextStatus.outMsg = flow.msg
            nextStatus.sender = flow.source
            nextStatus.receiver = flow.destination
        }   
	
        -- constraints for authAs'
        all alice: User | all bob: User | {
            one bob.(alice.authAs')
        }

        all curStatus : finishedStatus' | {
            (curStatus.receiver)->(curStatus.claimedAuth.User)->(User.(curStatus.claimedAuth)) in authAs'
        }

        all alice : (authAs' - authAs).User.User | all bob: alice.(authAs' - authAs).User | all role: bob.(alice.(authAs' - authAs)) {
            some curStatus : finishedStatus' | {
                alice = curStatus.receiver
                bob = curStatus.sender
                role = User.(curStatus.claimedAuth)
            }
        }
	
	
	-- constraints for receivedMessages'
	receivedMessages' = sentMessages' - interceptedMessages'
	
	-- constraints for hasMessages'
	all user : User - Attacker {
		synthesize[user.hasMessages', user.hasMessages + receivedMessages'.msg]
	}
	
        
	-- constraints for attacker
	DolevYaoAttacker[Attacker.hasMessages',interceptedMessages',sentMessages',Attacker.hasMessages]
        
}

-- Validation
pred ManInTheMiddleAttack[authAs: User->(User->User)]{
        some alice : User - Stranger - Attacker | some bob :  User - Stranger - Attacker - alice | some eve : Attacker | {
	        bob->Stranger in alice.authAs
	        eve->bob in alice.authAs
	        alice->Stranger in bob.authAs
	        eve->alice in bob.authAs
      }
}

pred success[authAs: User->(User->User)]{
    some alice : User - Stranger - Attacker | some bob :  User - Stranger - Attacker - alice | {
        bob->bob in alice.authAs
        alice->alice in bob.authAs
    }
}

pred SuccessVerify{
    some curState : State | {
         --success[curState.authAs]

         some curState.finishedStatus
         
    }
}

pred NetworkPartition{
    all curState : State | {
        curState.sentMessages = curState.interceptedMessages
    }
}

pred Secure{
    all curState : State | {
        not ManInTheMiddleAttack[curState.authAs]
    }
}

-- Configuration

pred DefaultSetting{
        -- make step linear
        all step: Step | {
            step in initStep.*nextStep
        }
        -- one final step
        one step: Step | finalStep[step]

        -- Stanger is just a signiture
        no Stranger & Status.sender 
        no Stranger & Status.receiver

        Message =  EncryptedMessage + ComposedMessage + RandomMessage + Key
}

trace<|State, initState, processState, _|> authMachine {
    DefaultSetting 
}

--run <|authMachine|> {SuccessVerify}  for  exactly 5 User, exactly 5 Key, exactly 7 State, exactly 10 Status, exactly 10 EncryptedMessage, exactly 2 ComposedMessage, exactly 5 RandomMessage, exactly 18 Message, exactly 20 NetworkFlow
--run <|authMachine|> {SuccessVerify NetworkPartition}  for  exactly 5 User, exactly 5 Key, exactly 7 State, exactly 10 Status, exactly 10 EncryptedMessage, exactly 2 ComposedMessage, exactly 5 RandomMessage, exactly 18 Message, exactly 20 NetworkFlow
check <|authMachine|> {Secure}  for  exactly 5 User, exactly 5 Key, exactly 9 State, exactly 20 Status, exactly 16 EncryptedMessage, exactly 4 ComposedMessage, exactly 5 RandomMessage, exactly 30 Message, exactly 30 NetworkFlow
