#lang forge
-- Message

sig Message {}

sig Key extends Message{
	paired: one Key,
	belongs: one User
}

sig ComposedMessage extends Message{
	subMessage: one Message->Message
}
sig EncryptedMessage extends Message{
	content: one Key->Message
}

sig RandomNumber extends Message{}

-- Role

sig User {}

one sig Stranger extends User{}

one sig Attacker extends User{}

pred composeMessage[mC: ComposedMessage, m1: Message, m2: Message]{
	mC.subMessage = m1->m2
}

pred encryptMessage[mE: EncryptedMessage, mP: Message, k: Key]{
	mE.content = k.paired->mP
}

pred UniqueMessage[m: one RandomNumber, u: User, hasMessages: User->Message]{
	m in u.hasMessages
	no m & (User - u).hasMessages
}

pred defaultAbility[totalMessage: Message, rawMessage: Message]{
       (totalMessage & ComposedMessage).subMessage in totalMessage->totalMessage
       (totalMessage & EncryptedMessage).content in (totalMessage & Key).paired->totalMessage
	totalMessage = rawMessage
				+ (totalMessage & ComposedMessage).subMessage.Message 				-- decompose
				+ Message.((totalMessage & ComposedMessage).subMessage) 			-- decompose
				+ (totalMessage & Key).((totalMessage & EncryptedMessage).content) 	-- decrypt
                                + totalMessage & ComposedMessage
			--	+ subMessage.(totalMessage->totalMessage) 							-- compose
				+ totalMessage & EncryptedMessage 			-- encrypt
}

-- Protocol

sig Step{}
sig Status{
	-- protocol status metadata
	claimedAuth : one User->User, -- claimer, claimed
	curStep : one Step,
	
	-- last update
	sender : one User,
	receiver : one User
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
        }
	
	-- all user has this key
	all user : User | {
		Key in user.hasMessages
	}
}

-- Bob receive an encrypted data, and add

pred regulateStep3[step: Step, hasMessages: User->Message]{
	all status : Status | status.curStep = step => {
		one inMessage : EncryptedMessage | 
		one plaintext : RandomNumber | {
		
			-- in Message Structure
			encryptMessage[inMessage, plaintext, belongs.(status.sender)]
			
			plaintext in (status.sender).hasMessages
			
			status->inMessage in AuthProtocol.validStatus
			
		}
		
	
	}
	step.(AuthProtocol.nextStep) = step -- final step
}

pred regulateStep2[step: Step, hasMessages: User->Message]{
	all status : Status | status.curStep = step => {
		one outMessage : EncryptedMessage | 
		one inMessage : EncryptedMessage | 
		one innerMessage : ComposedMessage |
		one plaintext : RandomNumber |
		one plaintext2 : RandomNumber | {
		
			-- in Message Structure
			encryptMessage[inMessage,innerMessage,belongs.(status.sender)]
			composeMessage[innerMessage, plaintext, plaintext2]
			
			
			plaintext in (status.sender).hasMessages
			
			
			-- out Message Structure
			encryptMessage[outMessage, plaintext2, belongs.(status.receiver)]
			
			status->inMessage in AuthProtocol.validStatus
			status->outMessage->(status.receiver) in AuthProtocol.action
		}
		
	
	}
	regulateStep3[step.(AuthProtocol.nextStep), hasMessages]
}

pred regulateStep1[step: Step, hasMessages: User->Message]{
	all status : Status | status.curStep = step => {
		status.curStep = step
                one outMessage : EncryptedMessage | 
		one innerMessage : ComposedMessage |
		one inMessage : EncryptedMessage | 
		one plaintext : RandomNumber - status.sender.hasMessages | 
		one plaintext2: RandomNumber | {
                        UniqueMessage[plaintext2, status.sender, hasMessages]
			-- in Message Structure
			encryptMessage[inMessage, plaintext, belongs.(status.sender)]
			
			-- out Message Structure
			composeMessage[innerMessage, plaintext, plaintext2]
			encryptMessage[outMessage, innerMessage, belongs.(status.receiver)]
			
			status->inMessage in AuthProtocol.validStatus
			status->outMessage->(status.receiver) in AuthProtocol.action
		}
			
	}	
	regulateStep2[step.(AuthProtocol.nextStep), hasMessages]
}

-- Alice send encrypted data to Bob
pred regulateStep0[step: Step, hasMessages: User->Message]{
	all status : Status | status.curStep = step =>{
		status.claimedAuth.User = status.sender
	
		one outMessage : EncryptedMessage | 
		one plaintext : RandomNumber | {
                        UniqueMessage[plaintext, status.sender, hasMessages]
                        encryptMessage[outMessage, plaintext, belongs.(status.receiver)]

                        status.(AuthProtocol.action) = outMessage->(status.receiver)
                        status.(AuthProtocol.validStatus) = plaintext
		}
	}
	regulateStep1[step.(AuthProtocol.nextStep), hasMessages]
}

pred initValidStatus[hasMessages: User->Message]{
	all step: AuthProtocol.initStep.*(AuthProtocol.nextStep) | {
		step not in step.^(AuthProtocol.nextStep)
	}
	regulateStep0[AuthProtocol.initStep, hasMessages]
}

one sig AuthProtocol {
	validStatus	: set Status->Message,
	action: set Status->Message->User, 			-- Status,  message, receiver,
	nextStep: set Step->Step,
	initStep: one Step
}

pred initiateAuth[nextStatus: Status, claimer: User,claimed: User, validator: User, messagesToSent: Networkflow]{
	nextStatus.claimedAuth = claimer->claimed
	nextStatus.curStep = AuthProtocol.initStep
	nextStatus.sender = claimer
	nextStatus.receiver = User
	no messagesToSent
}

pred protocolExecution [nextStatus: Status, curStatus: Status, message: Message, messagesToSent: User->Message->User]{
    
	no msg : message & curStatus.(AuthProtocol.validStatus) | {
		nextStatus = curStatus => no messagesToSent
		else { -- The status is intercepted and redirect to the attacker
			DolevProtocolIntercept[nextStatus, curStatus]
			no messagesToSent
		}
		
	}
 
	some message & curStatus.(AuthProtocol.validStatus) => {
		nextStatus.curStep = curStatus.curStep.(AuthProtocol.nextStep)
		nextStatus.sender = curStatus.receiver
		nextStatus.receiver = curStatus.sender
		nextStatus.receiver = Message.(curStatus.(AuthProtocol.action))
                let message = curStatus.(AuthProtocol.action).User |
                let user = Message.(curStatus.(AuthProtocol.action)) |
		messagesToSent = curStatus.receiver->message->user
	}

}

-- Attacker

pred DolevYaoAttacker[totalMessage: Message, interceptedMessages: User->Message->User, sentMessages: User->Message->User, rawMessage: Message]{
	interceptedMessages in sentMessages 								-- intercept
	defaultAbility[totalMessage, rawMessage + User.sentMessages.User]	-- overhear and synthesize
	Attacker.sentMessages.User in rawMessage							-- inject
}

pred DolevProtocolIntercept[nextStatus: Status, curStatus: Status]{
	nextStatus.claimedAuth = curStatus.claimedAuth
	nextStatus.curStep = curStatus.curStep
	nextStatus.sender = curStatus.sender
	nextStatus.receiver = Attacker
}

-- Exectution

sig State {
	status 				: set Status,
	newStatus			: set Status,
	finishedStatus		: set Status,
	authAs				: set User->User->User,  	-- receiver, sender, claimed_auth
	sentMessages 		: set User->Message->User, 	-- sender, message, receiver
	receivedMessages 	: set User->Message->User,	-- sender, message, receiver
	interceptedMessages : set User->Message->User,	-- sender, message, receiver
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
        initValidStatus[hasMessages]
        
	one finalStep : Step | {
                finalStep->finalStep in AuthProtocol.nextStep
		-- this step is final_step
		finishedStatus' = curStep.finalStep & status
	}
        
	-- add newStatus
        some newStatus' => newStatus'.curStep =  AuthProtocol.initStep 						-- only initStep allowed in new status	
	
   
	
	all initStatus : newStatus' - sender.Attacker | {
		initStatus.claimedAuth.User = User.(initStatus.claimedAuth) -- user are honest
		no initStatus.sender & initStatus.receiver 					-- no need for self auth
		initStatus.receiver->initStatus.sender in authAs'.Stranger 	-- no need for authed user
	}
	newStatus' in status'
	no finishedStatus' & status'
	
	-- constraints for status' and sentMessages'
	all nextStatus: status' - newStatus' | {
		no nextStatus.sender & nextStatus.receiver -- trapped
		one curStatus: status {
			nextStatus
			some message : Message | {
                                defaultAbility[message, curStatus.receiver.hasMessages + (curStatus.sender).sentMessages.(curStatus.receiver)]

                                some sender: User | some message: Message | some receiver: User | {
                                    --protocolExecution[nextStatus, curStatus, message, sender->message->receiver]
                                    sender->message->receiver in sentMessages'
                                } 
                        }
		} 
	}
	all user: (User - Attacker) | all message : user.sentMessages.User |
		some curStatus : status | {
			curStatus.receiver = user
			message in curStatus.(AuthProtocol.action).User	-- sent required message for protocol only
		}

        
	
        -- constraints for authAs'
        all alice: User | all bob: User | {
            one bob.(alice.authAs')
        }
        all alice: (authAs' - authAs).User.User | all bob : User.(authAs' - authAs).User {
            some curStatus : finishedStatus' | {
                alice = curStatus.receiver
                bob = curStatus.claimedAuth.User
                alice->bob->User.(curStatus.claimedAuth) in authAs'
            }
        }
	
	
	-- constraints for receivedMessages'
	receivedMessages' = sentMessages' - interceptedMessages'
	
	-- constraints for hasMessages'
	all user : User - Attacker {
		user.hasMessages' = user.hasMessages + User.receivedMessages'.user
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

pred Secure{
    all curState : State | {
        not ManInTheMiddleAttack[curState.authAs]
    }
}

trace<|State, initState, processState, _|> authMachine {}

run <|authMachine|> {}  for  exactly 5 User, exactly 5 Key, exactly 6 State, exactly 8 EncryptedMessage, exactly 8 ComposedMessage, exactly 5 RandomNumber, exactly 26 Message

