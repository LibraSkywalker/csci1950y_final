pred initProtocol[hasMessages: set User->Message]{ -- some common knowledge
	-- private key encryption
	all key : Key | {
		key.paired = key
	}
	
	all user : User | {
		# belongs.user = 1
	}
	# Key = # User
	
	-- all user has this key
	all user : User | {
		Key in user.hasMessages
	}
}

pred initValidStatus{
	all step: AuthProtocol.initStep.*nextstep | {
		step not in step.^nextstep
	}
	regulateStep0(AuthProtocol.initStep)
}


-- Alice send encrypted data to Bob
pred regulateStep0[step: Step]{
	all status : status.curStep = step | {
		status.claimedAuth.User = status.sender
	
		one outMessage : EncryptedMessage | {
			one plaintext : UniqueMessage[plaintext, status.sender] | {
				EncryptMessage[outMessage, plaintext, belongs.(status.receiver)]
			}
			status->outMessage->(status.receiver) in AuthProtocol.action
			status->plaintext in AuthProtocol.validStatus
		}
	}
	regulateStep1[step.nextstep]
}

-- Bob receive an encrypted data, and add

pred regulateStep1[step: Step]{
	all status : status.curStep = step | {
		
		one outMessage : EncryptMessage | 
		one innerMessage : ComposedMessage |
		one inMessage : EncryptMessage | 
		one plaintext : Message - status.sender.hasMessages | 
		one plaintext2: UniqueMessage[plaintext, status.sender] | {
			-- in Message Structure
			EncryptMessage[inMessage, plaintext, belongs.(status.sender)]
			
			-- out Message Structure
			ComposeMessage[innerMessage, plaintext, plaintext2]
			EncryptMessage[outMessage, innerMessage, belongs.(status.receiver)]
			
			status->inMessage in AuthProtocol.validStatus
			status->outMessage->(status.receiver) in AuthProtocol.action
		}
			
	}	
	regulateStep2[step.nextstep]
}

pred regulateStep2[step: Step]{
	all status : status.curStep = step | 
		one outMessage : EncryptMessage | 
		one inMessage : EncryptMessage | 
		one innerMessage : ComposedMessage |
		one plaintext : Message |
		one plaintext2 : Message | {
		
			-- in Message Structure
			EncryptMessage[inMessage,innerMessage,blongs.(status.sender)]
			ComposeMessage[innerMessage, plaintext, plaintext2]
			
			
			plaintext in (status.sender).hasMessages
			
			
			-- out Message Structure
			EncryptMessage[outMessage, plaintext2, belongs.(status.sender)]
			
			status->inMessage in AuthProtocol.validStatus
			status->outMessage->(status.receiver) in AuthProtocol.action
		}
		
	
	}
	regulateStep3[step.nextstep]
}

pred regulateStep3[step: Step]{
	all status : status.curStep = step | 
		one inMessage : EncryptMessage | 
		one plaintext : Message |
		
			-- in Message Structure
			EncryptMessage[inMessage, plaintext, belongs.(status.sender)]
			
			plaintext in (status.sender).hasMessages
			
			status->inMessage in AuthProtocol.validStatus
			
		}
		
	
	}
	step.nextstep = step # final step
}