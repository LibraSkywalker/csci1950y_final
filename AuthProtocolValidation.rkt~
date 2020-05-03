#lang forge
(require "NSPK.rkt")
-- Message

sig Message

sig Key extends Message{
	paired: one Key
	belongs: one User
}

sig ComposedMessage extends Message{
	subMessage: one Message->Message
}
sig EncryptedMessage extends Message{
	content: one Key->Message
}

-- Role

sig User {}

one sig Stranger extends User{}

one sig Attacker extends User{}

pred ComposeMessage[mC: ComposedMessage, m1: Message, m2: Message]{
	mC.subMessage = m1->m2
}

pred EncryptMessage[mE: EncryptedMessage, mP: Message, k: Key]{
	mE.content = k.paired->mP
}

pred UniqueMessage[m: Message, u: User]{
	m in u.hasMessages
	not m & (User - u).hasMessages
}

pred defaultAbility[totalMessage: Message, rawMessage: Message]{
	totalMessage = rawMessage
				+ (totalMessage & ComposedMessage).subMessage.Message 				-- decompose
				+ Message.((totalMessage & ComposedMessage).subMessage) 			-- decompose
				+ (totalMessage & Key).((totalMessage & EncryptedMessage).content) 	-- decrypt
				+ subMessage.(totalMessage->totalMessage) 							-- compose
				+ content.((totalMessage & Key).paired->User.hasMessages)) 			-- encrypt
}

-- Protocol

sig Step{}
sig Status{
	-- protocol status metadata
	claimedAuth : one User->User -- claimer, claimed
	curStep : one Step
	
	-- last update
	sender : one User
	receiver : one User
}

sig AuthProtocol {
	validStatus	: set Status->Message
	action: set Status->Message->User 			-- Status,  message, receiver,
	nextStep: set Step->Step
	initStep: one Step
}

pred initiateAuth[nextStatus: Status, claimer: User,claimed: User, validator: User, messagesToSent: Set User->Message->User]{
	nextStatus.claimedAuth = claimer->claimed
	nextStatus.step = AuthProtocol.initStep
	nextStatus.sender = claimer
	nextStatus.receiver = User
	no messagesToSent
}

pred protocolExecution [nextStatus: Status, curStatus: Status, message: Set Message, messagesToSent: Set User->Message->User]{
	no msg : message & curStatus.(AuthProtocol.validStatus) => {
		nextStatus = curStatus => no messagesToSent
		else => { -- The status is intercepted and redirect to the attacker
			DolevProtocolIntercept[nextStatus, curStatus]
			no messagesToSent
		}
		
	}
	else => {
		nextStatus.step = curStatus.step.(AuthProtocol.nextStep)
		nextStatus.sender = curStatus.receiver
		nextStatus.receiver = curStatus.sender
		nextStatus.receiver = Message.(curStatus.(AuthProtocol.action)))
		messagesToSent = curStatus.receiver->curStatus.(AuthProtocol.action)
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
	nextStatus.step = curStatus.step
	nextStatus.sender = curStatus.sender
	nextStatus.receiver = Attacker
}

-- Exectution

sig State {
	status 				: set Status
	newStatus			: set Status
	finishedStatus		: set Status
	authAs 				: set User->User->User  	-- receiver, sender, claimed_auth
	sentMessages 		: set User->Message->User 	-- sender, message, receiver
	receivedMessages 	: set User->Message->User	-- sender, message, receiver
	interceptedMessages : set User->Message->User	-- sender, message, receiver
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
	initValidStatus
	-- remove finishedStatus
	one finalStep : finalStep->finalStep in AuthProtocol.nextStep | {
		-- this step is final_step
		finishedStatus' = step.finalStep & status
	}
		
	-- add newStatus
	newStatus'.step =  AuthProtocol.initStep 						-- only initStep allowed in new status	
	
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
			some message : defaultAbility(message, curStatus.receiver.hasMessages + (curStatus.sender).sentMessages.(curStatus.receiver)) |
				some messageToSent : protocolExecution[nextStatus, curStatus, curStatus.receiver, message, messageToSent] | {
					messageToSent in sentMessages'
				}
		}
	}
	all user: (User - Attacker) | all message : user->sentMessages |
		some curStatus : status | {
			curStatus.receiver = user
			message in curStatus.(AuthProtocol.action).User		-- sent required message for protocol only
		}
		
	
	-- constraints for authAs'
	all auth: authAs' - authAs | {
		some curStatus : finishedStatus' | {
			auth = (curStatus.receiver)->(curStatus.claimer)->(curStatus.claimed)
		}
	}
	all auth: authAs - authAs' | {
		some curStatus : finishedStatus' | {
			auth = (curStatus.receiver)->(curStatus.claimer)->Stranger
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
pred ManInTheMiddleAttack[alice: User, bob: User, eve: Attacker, authAs: set User->User->User]{
	bob->Stranger in alice->authAs
	eve->bob in alice->authAs
	alice->Stranger in bob->authAs
	eve->alice in bob->authAs
}